/*------------------------------------------------------------------------*/
#ifndef NELIMINATION
/*------------------------------------------------------------------------*/

static bool
more_elimination_candidates (struct satch *solver)
{
  return solver->statistics.marked_eliminate >
    solver->limits.eliminate.marked;
}

#ifndef NSUBSUMPTION

static bool
more_subsumption_candidates (struct satch *solver)
{
  return solver->statistics.marked_subsume > solver->limits.subsume.marked;
}

#endif

static bool
eliminating (struct satch *solver)
{
#ifdef NCDCL
  if (solver->level)
    return false;
#endif
  if (!more_elimination_candidates (solver))
#ifndef NSUBSUMPTION
    if (!more_subsumption_candidates (solver))
#endif
      return false;
#ifndef NINPROCESSING
  return solver->limits.eliminate.conflicts < CONFLICTS;
#else
  return !solver->statistics.eliminations;
#endif
}

/*------------------------------------------------------------------------*/

// The code for switching from sparse to dense mode and back heavily relies
// on how watches are organized ('NVIRTUAL' or even 'NBLOCK' is defined).

#ifndef NVIRTUAL

// This is the default routine for flushing all redundant watches where we
// use virtual binary clauses and blocking literals.

// It is the most complex variant because binary clauses reside in watches
// only and thus the redundant binary clauses have to be saved while the
// irredundant ones are kept.  The redundant-clause watches are flushed
// completely, while for the redundant-clause watches we remove the header.

// Furthermore, since in dense mode we only have clause references as watches
// we need to use the same mechanism as for reasons to store binary clauses
// (actually only the other literal) through tagged clause pointers.

static void
flush_redundant_watches (struct satch *solver, bool new_fixed)
{
  assert (EMPTY_STACK (solver->binaries));
  const struct flags *const flags = solver->flags;
  for (all_literals (lit))
    {
      struct watches *watches = solver->watches + lit;
      const union watch *const end = watches->end;
      union watch *q = watches->begin, *p = q;
      const bool lit_active = new_fixed ? true : flags[INDEX (lit)].active;
      while (p != end)
	{
	  struct header header = p->header;
	  if (header.binary)
	    {
	      const unsigned other = header.blocking;
	      const bool redundant = header.redundant;
	      const bool other_active =
		new_fixed ? true : flags[INDEX (other)].active;

	      if (lit_active && other_active)
		{
		  if (header.redundant)
		    {
		      if (lit < other)
			{
			  PUSH (solver->binaries, lit);
			  PUSH (solver->binaries, other);
			}
		    }
		  else
		    q++->clause = tag_binary_clause (false, other);
		}
	      else
		delete_binary (solver, redundant, lit, other);

	      p++;
	    }
	  else
	    {
	      if (!header.redundant)
		{
		  struct clause *c = p[1].clause;
		  if (!new_fixed || !c->garbage)
		    q++->clause = c;
		}

	      p += 2;
	    }
	}
      watches->end = q;
      if (EMPTY_STACK (*watches))
	RELEASE_STACK (*watches);
    }
  LOG ("saved %zu redundant binary clauses",
       SIZE_STACK (solver->binaries) / 2);
}

#elif !defined(NBLOCK)

// With blocking literals but without virtual clauses the watches all have
// both a header and a clause.  We always drop the header (the blocking
// literal) and in addition flush the reference to redundant clauses.

static void
flush_redundant_watches (struct satch *solver, bool new_fixed)
{
  for (all_literals (lit))
    {
      struct watches *watches = solver->watches + lit;
      const union watch *const end = watches->end;
      union watch *q = watches->begin;
      for (const union watch * p = q; p != end; p += 2)
	if (!p->header.redundant)
	  {
	    struct clause *c = p[1].clause;
	    if (!new_fixed || !c->garbage)
	      *q++ = p[1];
	  }
      watches->end = q;
      if (EMPTY_STACK (*watches))
	RELEASE_STACK (*watches);
    }
}

#else

// The simplest case without blocking literals (and also without virtual
// binary clauses) we just flush redundant clauses. This has the same effect
// as in the previous case (no virtual binary clauses but with blocking
// literals) and thus when working in dense mode code we only need to
// distinguish between having virtual binary clauses or not.

static void
flush_redundant_watches (struct satch *solver, bool new_fixed)
{
  for (all_literals (lit))
    {
      struct watches *watches = solver->watches + lit;
      const union watch *const end = watches->end;
      union watch *q = watches->begin;
      struct clause *c;
      for (const union watch * p = q; p != end; p++)
	if (!(c = p->clause)->redundant && (!new_fixed || !c->garbage))
	  *q++ = *p;
      watches->end = q;
      if (EMPTY_STACK (*watches))
	RELEASE_STACK (*watches);
    }
}

#endif

static void
connect_occurrences_in_irredundant_clauses (struct satch *solver)
{
  assert (solver->dense);
  for (all_irredundant_clauses (c))
    {
      const unsigned *const lits = c->literals;
      const unsigned *const end = lits + c->size;
      for (const unsigned *p = lits + 2; p != end; p++)
       if (!c->garbage)
         connect_literal (solver, *p, c);
    }
}

static void
switch_to_dense_mode (struct satch *solver)
{
  LOG ("switching to dense mode");
  assert (!solver->dense);
  bool new_fixed = solver->limits.eliminate.fixed < solver->statistics.fixed;
  if (new_fixed)
    mark_irredundant_clauses_as_garbage_if_satisfied (solver);
  flush_redundant_watches (solver, new_fixed);
  solver->dense = true;
  connect_occurrences_in_irredundant_clauses (solver);
}

/*------------------------------------------------------------------------*/

#ifndef NVIRTUAL

// With virtual binary clauses we need to make sure to keep the irredundant
// binary clauses in the watcher stacks but otherwise drop all references.

static void
disconnect_all_clauses (struct satch *solver)
{
  assert (solver->dense);
  const struct flags *const flags = solver->flags;
  for (all_literals (lit))
    {
      struct watches *watches = solver->watches + lit;
      const union watch *const end = watches->end;
      union watch *q = watches->begin;
      struct clause *c;
      bool lit_eliminated = flags[INDEX (lit)].eliminated;
      for (const union watch * p = q; p != end; p++)
	if (is_tagged_clause (c = p->clause))
	  {
	    const unsigned other = tagged_clause_to_literal (c);
	    const bool other_eliminated = flags[INDEX (other)].eliminated;
	    if (!lit_eliminated && !other_eliminated)
	      {
		union watch watch;
		watch.header.binary = true;
		watch.header.redundant = false;
		watch.header.blocking = other;
		*q++ = watch;
	      }
	    else
	      delete_binary (solver, false, lit, other);
	  }
      watches->end = q;
    }
}

#else

static void
disconnect_all_clauses (struct satch *solver)
{
  assert (solver->dense);
  for (all_literals (lit))
    CLEAR_STACK (solver->watches[lit]);
}

#endif

#ifndef NVIRTUAL

static void
watch_saved_redundant_binaries (struct satch *solver)
{
  const unsigned *begin = solver->binaries.begin;
  const unsigned *end = solver->binaries.end;
  const struct flags *const flags = solver->flags;
  for (const unsigned *p = begin; p != end; p += 2)
    {
      const unsigned i[2] = { INDEX (p[0]), INDEX (p[1]) };
      const struct flags f[2] = { flags[i[0]], flags[i[1]] };
      const bool eliminated[2] = { f[0].eliminated, f[1].eliminated };
      if (!eliminated[0] && !eliminated[1])
	{
	  watch_binary (solver, true, p[0], p[1]);
	  watch_binary (solver, true, p[1], p[0]);
	}
      else
	delete_binary (solver, true, p[0], p[1]);
    }
  CLEAR_STACK (solver->binaries);
}

#endif

static void
watch_clauses (struct satch *solver, struct clauses *clauses)
{
  for (all_pointers_on_stack (struct clause, c, *clauses))
      watch_clause (solver, c);
}

static void
switch_to_sparse_mode (struct satch *solver)
{
  LOG ("switching back to sparse mode");
  assert (solver->dense);
  disconnect_all_clauses (solver);
  solver->dense = false;
#ifndef NVIRTUAL
  watch_saved_redundant_binaries (solver);
#endif
  watch_clauses (solver, &solver->irredundant);
  watch_clauses (solver, &solver->redundant);
}

/*------------------------------------------------------------------------*/

// Check whether a (redundant) clause contains an eliminated literal.

static bool
clause_eliminated (struct satch *solver, struct clause *c)
{
  assert (c->redundant);	// Coincidentally.
  assert (!solver->level);
  const struct flags *const flags = solver->flags;
  for (all_literals_in_clause (lit, c))
    if (flags[INDEX (lit)].eliminated)
      return true;
  return false;
}

static void
mark_satisfied_eliminated_redundant_clauses_garbage (struct satch *solver)
{
  for (all_redundant_clauses (c))
    if (!c->garbage)
      {
	if (clause_eliminated (solver, c))
	  mark_garbage (solver, c, "eliminated");
	else if (clause_satisfied (solver, c))
	  mark_garbage (solver, c, "root-level satisfied");
      }
}

// The irredundant eliminated clauses have been marked explicitly already
// but we still need to mark redundant clauses with eliminated variables.

static void
mark_and_collect_garbage_clauses_after_elimination (struct satch *solver)
{
  assert (solver->dense);	// No flushing in 'clause_satisfied'!

  if (solver->limits.eliminate.fixed < solver->statistics.fixed)
    mark_irredundant_clauses_as_garbage_if_satisfied (solver);

  mark_satisfied_eliminated_redundant_clauses_garbage (solver);

  {
    size_t bytes = 0, count = 0;
    delete_garbage_clauses (solver, &solver->irredundant, &bytes, &count);
    delete_garbage_clauses (solver, &solver->redundant, &bytes, &count);

    // We report on how many clauses we collected during elimination.

    message (solver, 2, "elimination", solver->statistics.eliminations,
	     "collected %zu clauses (%zu bytes, %.0f MB)",
	     count, bytes, bytes / (double) (1u << 20));

    ADD (collected, bytes);
  }
}

/*------------------------------------------------------------------------*/

#ifndef NSUBSUMPTION

// Assume 'size' literals have been marked.  Then try to find a clause
// different from 'skip' in which the literal 'lit' occurs and has all the
// marked literals.  This clause is then subsumed and marked garbage.  We also
// perform strengthening through self-subsuming resolution, which removes
// individual literals from clauses which are almost subsumed except for one
// literal which occurs negated.

// The clause literal 'traversed' denotes a literal whose watches are
// currently traversed (the 'lit' in 'backward_subsume_literal').  If we
// modify its watches we have to abort that traversals since iterators
// (pointers into the stack) become invalid.

static bool
backward_subsume_marked (struct satch *solver,
			 unsigned size, unsigned lit,
			 struct clause *skip, unsigned traversed)
{
#ifdef NSTRENGTHENING
  (void) traversed;
#endif
  assert (solver->flags[INDEX (lit)].active);

  struct watches *const watches = solver->watches + lit;
  const signed char *const values = solver->values;
  const signed char *const marks = solver->marks;

  bool touched = false;		// Traversed literal watches touched.

  assert (!solver->level);

  uint64_t ticks = 1 + CACHE_LINES_OF_STACK (watches);

  ADD (subsumption_ticks, ticks);

  const union watch *const end_of_watches = watches->end, *p;
  union watch *q = watches->begin;

  for (p = q; p != end_of_watches; p++)
    {
      const union watch watch = *q++ = *p;
#ifdef NVIRTUAL
      if (solver->inconsistent)
	continue;
#endif
      struct clause *c = watch.clause;
      if (c == skip)
	continue;

#ifndef NVIRTUAL
      if (is_tagged_clause (c))
	{
	  // We use 'remove_duplicated_virtual_binary_clauses' instead.
	  continue;
	}
      else
#endif
	{
	  ticks++;
	  if (c->garbage)
	    continue;
	}

      if (c->size < size)
	continue;

      bool satisfied = false;	// Clause actually satisfied.
      unsigned clashed = 0;	// How many clashing literals.
      unsigned found = 0;	// How many literals found.
#ifndef NSTRENGTHENING
      unsigned clashing = INVALID;	// The last clashing literal.
#endif
      for (all_literals_in_clause (other, c))
	{
	  const signed char value = values[other];
	  if (value > 0)
	    {
	      satisfied = true;
	      break;
	    }
	  if (value < 0)
	    continue;
	  const signed char mark = marked_literal (marks, other);
	  if (!mark)
	    continue;
	  if (mark < 0)
	    {
#ifndef NSTRENGTHENING
	      if (clashed++)
		break;
	      clashing = other;
#else
	      clashed = 1;
	      break;
#endif
	    }
	  else
	    assert (mark > 0);
	  found++;
	}

#ifndef NSTRENGTHENING
      if (clashed > 1)
	continue;
#else
      if (clashed)
	continue;
#endif
      if (satisfied)
	{
	  mark_garbage (solver, c, "root-level satisfied");
	  continue;
	}

      if (found < size)
	continue;

      assert (found == size);

#ifndef NSTRENGTHENING		// Begin of strengthening code.

      if (clashed)
	{
#ifndef NSUBSUMPTIONLIMITS
	  {
	    const size_t occs = SIZE_STACK (solver->watches[clashing]);
	    if (occs >= strengthening_occurrence_limit)
	      continue;
	  }
#endif
	  assert (clashed == 1);
	  assert (clashing != INVALID);
	  LOGCLS (c, "single clashing literal %s", LOGLIT (clashing));

	  // The negation of this assertion as a coverage hole was never
	  // triggered, It could be accommodated by setting 'touched = true'
	  // in this case, but as it never happens we added this assertion.

	  assert (clashing != traversed);

#ifdef NVIRTUAL
	  unsigned unit = INVALID;
	  if (c->size == 2)
	    {
	      for (all_literals_in_clause (other, c))
		if (other != clashing)
		  assert (unit == INVALID), unit = other;
	      assert (unit != INVALID);

	      const signed char value = solver->values[unit];
	      assert (value <= 0);
	      if (value < 0)
		{
		  trace_and_check_empty_addition (solver);
		  LOG ("inconsistent unit %s resolved", LOGLIT (unit));
		  solver->inconsistent = true;
		  touched = true;
		  continue;
		}
	    }
#endif
	  trace_and_check_clause_addition (solver, c, clashing);
	  trace_and_check_clause_deletion (solver, c);

	  mark_eliminate_literal (solver, clashing);
#ifdef NVIRTUAL
	  if (c->size == 2)
	    {
	      LOG ("resolved unit %s", LOGLIT (unit));
	      assert (unit != INVALID);
	      assert (!solver->values[unit]);
	      assign (solver, unit, 0, false);
	    }
	  else
#endif
	    {
	      assert (c->size > 2);
	      if (lit == clashing)
		{
		  LOGCLS (c, "disconnecting %s from", LOGLIT (lit));
		  q--;
		}
	      else
		{
		  ticks++;
		  disconnect_literal (solver, clashing, c);
		}

	      for (all_literals_in_clause (other, c))
		if (other != clashing)
		  mark_subsume_literal (solver, other);
	    }

#ifndef NVIRTUAL

	  // Ternary clauses become virtual binary clauses.

	  if (c->size == 3)
	    {
	      c->garbage = true;
	      unsigned first = INVALID, second = INVALID;

	      for (all_literals_in_clause (other, c))
		if (other != clashing)
		  {
		    if (first == INVALID)
		      first = other;
		    else
		      {
			assert (second == INVALID);
			second = other;
		      }
		    disconnect_literal (solver, other, c);
		  }
	      assert (first != INVALID);
	      assert (second != INVALID);
	      connect_literal (solver, first, tag_binary_clause (0, second));
	      connect_literal (solver, second, tag_binary_clause (0, first));
	      touched = (first == traversed || second == traversed);
	      ticks += 2;
	    }
	  else
#else
	  if (c->size > 2)
#endif
	    {
	      // Keep clause as is but remove a literal and reduce size.

	      unsigned *r = c->literals;
	      const unsigned *end_of_literals = r + c->size;
	      while (assert (r != end_of_literals), *r != clashing)
		r++;
	      while (++r != end_of_literals)
		r[-1] = *r;

	      c->size--;
#ifndef NGLUE
	      assert (!c->glue);
#endif
#ifndef NCACHE
	      c->search = 0;
#endif
	      LOGCLS (c, "strengthened");
	      INC (strengthened);
	    }
	}
      else
#endif // if '#ifndef NSTRENGTHENING' so end of strengthening code.

	{
	  mark_garbage (solver, c, "subsumed");
	  INC (subsumed);
	}
    }
  watches->end = q;
  if (EMPTY_STACK (*watches))
    RELEASE_STACK (*watches);

  ADD (subsumption_ticks, ticks);

#ifdef LOGGING
  if (touched)
    LOG ("watches of traversed literal %s touched", LOGLIT (traversed));
#endif

  return touched;
}

// Use the given clause to subsume other connected clauses.

// We only traverse the occurrence list of a single literal in the clause
// with the smallest number of occurrences to find subsumed clauses and also
// bound the maximum size of that list as well as the size of clauses.

// Furthermore only clauses with all literals (actually variables) marked as
// subsume candidate will be considered, since newly added clauses will mark
// their variables as subsume candidates.

// If the watch list of the 'traversed' literals is modified we return 'true'
// in order for the calling function ('backward_subsume_literal') to restart
// the watch list traversal (because its iterators became invalid).

static bool
backward_subsume_with_clause (struct satch *solver,
			      struct clause *c, unsigned traversed)
{
#ifndef NVIRTUAL
  if (!is_temporary_binary (solver, c))
#endif
    {
      assert (!c->subsumed);
      c->subsumed = true;
    }

  assert (!solver->level);
  LOGCLS (c, "backward subsumption with");
  assert (!c->redundant);

  bool satisfied = false;	// Clause 'c' satisfied.
  bool touched = false;		// Literal 'traverse' watches touched.
  bool subsume = true;		// All literals in 'c' marked 'subsume'.

  uint64_t min_pos_occs = UINT64_MAX;
  uint64_t min_neg_occs = UINT64_MAX;
  unsigned min_pos_lit = INVALID;
  unsigned min_neg_lit = INVALID;

  unsigned actual_size = 0;

  const struct watches *const watches = solver->watches;
  const struct flags *const flags = solver->flags;
  const signed char *values = solver->values;
  signed char *marks = solver->marks;

  uint64_t ticks = 2;		// Clause plus watch list.

  for (all_literals_in_clause (lit, c))
    {
      signed char value = values[lit];

      if (value > 0)
	{
	  LOG ("contains satisfied literal %s", LOGLIT (lit));
	  satisfied = true;
	  break;
	}

      if (value < 0)
	continue;

      const unsigned idx = INDEX (lit);
      if (!flags[idx].subsume)
	{
	  LOG ("contains non-subsumption candidate %s", LOGVAR (idx));
	  subsume = false;
	  break;
	}

      // Otherwise mark the literal for the subsumption check.

      mark_literal (marks, lit);
      actual_size++;

      ticks++;

      const size_t pos_occs = SIZE_STACK (watches[lit]);
      if (pos_occs < min_pos_occs)
	min_pos_occs = pos_occs, min_pos_lit = lit;

      const unsigned not_lit = NOT (lit);

      const size_t neg_occs = SIZE_STACK (watches[not_lit]);
      if (neg_occs < min_neg_occs)
	min_neg_occs = neg_occs, min_neg_lit = not_lit;
    }

  ADD (subsumption_ticks, ticks);

  if (satisfied)
    {
#ifndef NVIRTUAL
      if (!is_temporary_binary (solver, c))
#endif
	mark_garbage (solver, c, "root-level satisfied");
    }
  else if (subsume)
    {
      LOG ("actual size %u %s clause size %u", actual_size,
	   actual_size < c->size ? "smaller" : "matches", c->size);

#ifndef NSUBSUMPTIONLIMITS
      if (min_pos_occs <= subsumption_occurrence_limit)
#endif
	{
	  COVER (min_pos_lit == INVALID);
	  assert (min_pos_lit != INVALID);

	  LOG ("minimum positive occurrences %" PRIu64 " literal %s",
	       min_pos_occs, LOGLIT (min_pos_lit));

	  if (backward_subsume_marked (solver, actual_size,
				       min_pos_lit, c, traversed))
	    touched = true;
	}
#ifdef NVIRTUAL
      if (!solver->inconsistent && !solver->values[min_neg_lit])
#endif
#ifndef NSUBSUMPTIONLIMITS
	if (min_neg_occs <= subsumption_occurrence_limit)
#endif
	  {
	    COVER (min_neg_lit == INVALID);
	    assert (min_neg_lit != INVALID);

	    LOG ("minimum negative occurrences %" PRIu64 " literal %s",
		 min_neg_occs, LOGLIT (min_neg_lit));

	    if (backward_subsume_marked (solver, actual_size,
					 min_neg_lit, c, traversed))
	      touched = true;
	  }
    }

  for (all_literals_in_clause (lit, c))
    unmark_literal (marks, lit);

  return touched;
}

static void
backward_subsume_literal (struct satch *solver, unsigned lit)
{
#ifdef NVIRTUAL
  if (solver->inconsistent || solver->values[lit])
    return;
#endif

  INC (subsumption_ticks);

  const struct watches *const watches = solver->watches + lit;
#ifndef NSUBSUMPTIONLIMITS
  if (SIZE_STACK (*watches) > subsumption_occurrence_limit)
    return;
#endif

  LOG ("backward subsumption with clauses containing literal %s",
       LOGLIT (lit));

  uint64_t ticks = CACHE_LINES_OF_STACK (watches);

RESTART:			// If 'watches' touched (added or removed watches).

  for (all_elements_on_stack (union watch, watch, *watches))
    {
      struct clause *c = watch.clause;
#ifndef NVIRTUAL
      if (is_tagged_clause (c))
	c = untag_clause (solver, 0, lit, c);	// 1st temporary
      else
#endif
	{
	  ticks++;
	  if (c->garbage || c->subsumed)
	    continue;
	}
#ifndef NSUBSUMPTIONLIMITS
      if (c->size <= subsumption_clause_size_limit)
#endif
	if (backward_subsume_with_clause (solver, c, lit))
	  {
#ifdef NVIRTUAL
	    if (solver->inconsistent || solver->values[lit])
	      break;
#endif
	    LOG ("need to restart traversing %s watches", LOGLIT (lit));
	    goto RESTART;
	  }
    }

  ADD (subsumption_ticks, ticks);
}

#ifndef NVIRTUAL

// In 'backward_subsume_marked' we skip over tagged clauses because if such a
// tagged clause is subsumed the watch has to be removed immediately instead
// of marking it 'garbage'.  This is pretty awkward in that context and thus
// we implement a dedicated routine below to just do that.  It actually does
// all virtual binary clause (self-) subsumption of that literal in one go
// and thus we also do not enforce an occurrence limit.

static bool
remove_duplicated_virtual_binary_clauses (struct satch *solver, unsigned lit)
{
  LOG ("removing duplicated virtual binary clauses with %s", LOGLIT (lit));
  assert (solver->flags[INDEX (lit)].active);
  assert (!solver->level);

  struct watches *const watches = solver->watches + lit;
  const union watch *const end = watches->end;
  union watch *q = watches->begin, *p = q;

  uint64_t ticks = 1 + cache_lines (watches->begin, watches->end);

  signed char *marks = solver->marks;
  bool assigned = false;

  while (!assigned && p != end)
    {
      const union watch watch = *p++;
      struct clause *c = watch.clause;
      if (is_tagged_clause (c))
	{
	  const unsigned other = tagged_clause_to_literal (c);
	  const signed char mark = marked_literal (marks, other);
	  if (mark > 0)
	    {
	      really_delete_binary (solver, false, lit, other);
	      struct clause *d = tag_binary_clause (false, lit);
	      disconnect_literal (solver, other, d);
	      INC (subsumed);
	      ticks++;
	      continue;
	    }
	  if (mark < 0)
	    {
	      LOG ("self-subsuming virtual binary unit %s", LOGLIT (lit));
	      trace_and_check_unit_addition (solver, lit);
	      INC (strengthened);
	      assign (solver, lit, 0, true);
	      assigned = true;
	    }
	  else
	    mark_literal (marks, other);
	}
      *q++ = watch;
    }

  for (const union watch * r = watches->begin; r != q; r++)
    if (is_tagged_clause (r->clause))
      unmark_literal (marks, tagged_clause_to_literal (r->clause));

  while (p != end)
    *q++ = *p++;

  watches->end = q;

  ADD (subsumption_ticks, ticks);

  return !assigned;
}

#endif

static void
backward_subsume_variable (struct satch *solver, unsigned idx)
{
  LOG ("backward subsumption with clauses containing %s", LOGVAR (idx));
  assert (solver->flags[idx].subsume);
  assert (solver->flags[idx].active);

  const unsigned lit = LITERAL (idx);
  const unsigned not_lit = NOT (lit);
#ifndef NVIRTUAL
  if (!remove_duplicated_virtual_binary_clauses (solver, lit))
    return;
  if (!remove_duplicated_virtual_binary_clauses (solver, not_lit))
    return;
#endif
  backward_subsume_literal (solver, lit);
  backward_subsume_literal (solver, not_lit);

  solver->flags[idx].subsume = 2;
}

#ifndef NSUBSUMPTIONLIMITS

static bool
subsumption_ticks_limit_hit (struct satch *solver)
{
  return solver->statistics.subsumption_ticks > solver->limits.subsume.ticks;
}

#endif

static void
full_backward_subsumption (struct satch *solver)
{
  if (!more_subsumption_candidates (solver))
    return;

  START (subsume);
  const uint64_t subsumptions = INC (subsumptions);

  LOG ("backward subsumption with clauses containing subsume candidates");

  struct flags *flags = solver->flags;

  uint64_t total_subsumed = 0, total_strengthened = 0;
  uint64_t strengthened;
  unsigned round = 0;

  do
    {
      round++;

      const uint64_t subsumed_before = solver->statistics.subsumed;
      const uint64_t strengthened_before = solver->statistics.strengthened;
      const unsigned remaining = solver->statistics.remaining;
      unsigned scheduled = 0, tried = 0;

      for (all_variables (idx))
	{
	  struct flags *f = flags + idx;
	  if (f->active && (f->subsume &= 1))
	    scheduled++;
	}

      for (all_variables (idx))
	{
	  struct flags *f = flags + idx;
	  if (f->active && f->subsume)
	    {
	      backward_subsume_variable (solver, idx);
	      tried++;
#ifndef NSUBSUMPTIONLIMITS
	      if (subsumption_ticks_limit_hit (solver))
		{
		  message (solver, 4, "subsumption", subsumptions,
			   "subsumption ticks limit hit");
		  break;
		}
#endif
	    }
	}

      message (solver, 3, "subsumption", subsumptions,
	       "tried %u variables %.0f%% of %u scheduled %.0f%%"
	       " in round %u", tried, percent (tried, scheduled),
	       scheduled, percent (scheduled, remaining), round);

      uint64_t subsumed = solver->statistics.subsumed - subsumed_before;
      strengthened = solver->statistics.strengthened - strengthened_before;

      total_subsumed += subsumed;
      total_strengthened += strengthened;

      message (solver, 3, "subsumption", subsumptions,
	       "subsumed %" PRIu64 " and strengthened %" PRIu64
	       " clauses in round %u", subsumed, strengthened, round);

      report (solver, 1 + !(subsumed + strengthened), 's');
#ifndef NSUBSUMPTIONLIMITS
      if (round >= subsumption_rounds)
	break;
      if (subsumption_ticks_limit_hit (solver))
	break;
#endif
    }
  while (!solver->inconsistent && strengthened);

  for (all_irredundant_clauses (c))
    c->subsumed = false;

  unsigned kept = 0;
  for (all_variables (idx))
    {
      struct flags *f = flags + idx;
      if (f->active & (f->subsume & 1))
	kept++;
    }

  message (solver, 3, "subsumption", subsumptions,
	   "keeping %u variables scheduled %.0f%%",
	   kept, percent (kept, solver->statistics.remaining));

  if (!kept)
    solver->limits.subsume.marked = solver->statistics.marked_subsume;

  message (solver, 2, "subsumption", subsumptions,
	   "subsumed %" PRIu64 " and strengthened %" PRIu64
	   " clauses in %u rounds",
	   total_subsumed, total_strengthened, round);

  STOP (subsume);
}

#endif

/*------------------------------------------------------------------------*/

// Flush out garbage (satisfied and eliminated) clause occurrences.  Returns
// the remaining number of occurrences or 'elimination_occurrence_limit + 1'
// if a clause exceeds the elimination clause size limit or there are too
// many, i.e., more than 'elimination_occurrence_limit' remaining.

static unsigned
actual_number_of_occurrences (struct satch *solver, unsigned lit)
{
#ifndef NELIMINATIONLIMITS
  assert (elimination_occurrence_limit < UINT_MAX);
#endif
  assert (!solver->flags[INDEX (lit)].fixed);

  struct watches *watches = solver->watches + lit;
#ifndef NVIRTUAL
  signed char *values = solver->values;
#endif

  union watch *begin = watches->begin, *q = begin;
  const union watch *end = watches->end, *p = q;

  uint64_t ticks = 1;		// To access 'watches'.
  unsigned res = 0;

  while (p != end)
    {
      const union watch watch = *p++;

      struct clause *c = watch.clause;
#ifndef NVIRTUAL
      if (is_tagged_clause (c))
	{
	  const unsigned other = tagged_clause_to_literal (c);
	  if (values[other] > 0)
	    {
	      really_delete_binary (solver, false, lit, other);
	      struct clause *d = tag_binary_clause (false, lit);
	      disconnect_literal (solver, other, d);
	      ticks++;
	      continue;
	    }
	}
      else
#endif
	{
	  ticks++;
	  if (mark_garbage_if_satisfied (solver, c))
	    continue;
	}

      *q++ = watch;
      res++;

#ifndef NELIMINATIONLIMITS
      if (res > elimination_occurrence_limit)
	break;
#ifndef NVIRTUAL
      if (!is_tagged_clause (c))
#endif
	if (c->size > elimination_clause_size_limit)
	  {
	    res = elimination_occurrence_limit + 1;
	    break;
	  }
#endif
    }

  ticks += cache_lines (begin, q);
  ADD (elimination_ticks, ticks);

  while (p != end)
    *q++ = *p++;

  watches->end = q;
  if (EMPTY_STACK (*watches))
    RELEASE_STACK (*watches);

  return res;
}

// Check if the given variable matches is still active, its clauses stay
// below the clause size limit and it does not occur too often.

static bool
can_be_eliminated (struct satch *solver, unsigned pivot_idx)
{
  const struct flags *const f = solver->flags + pivot_idx;
  if (!f->active)
    return false;
  if (!f->eliminate)
    return false;

  const unsigned lit = LITERAL (pivot_idx);
  const unsigned not_lit = NOT (lit);

#ifndef NELIMINATIONLIMITS

  const uint64_t pos = actual_number_of_occurrences (solver, lit);
  const uint64_t neg = actual_number_of_occurrences (solver, not_lit);

  if (pos && neg > elimination_occurrence_limit)
    return false;

  if (neg && pos > elimination_occurrence_limit)
    return false;

#else

  (void) actual_number_of_occurrences (solver, lit);
  (void) actual_number_of_occurrences (solver, not_lit);

#endif

  return true;
}

// Check whether the given variable produces few resolvents and add them to
// the resolvents stack.  The limit is the number of original clauses.

// Process unit and empty clauses eagerly though which also requires that we
// need to check antecedent clauses (again) and later also the saved
// resolvents for being satisfied (or falsified).

static bool
produces_few_resolvents (struct satch *solver, unsigned pivot_idx)
{
  assert (!solver->inconsistent);

  const unsigned pivot = LITERAL (pivot_idx);
  const unsigned not_pivot = NOT (pivot);

  struct watches *const pos_watches = solver->watches + pivot;
  struct watches *const neg_watches = solver->watches + not_pivot;

  assert (EMPTY_STACK (solver->resolvents));

  LOG ("trying to eliminate %s", LOGVAR (pivot_idx));

  const size_t pos_count = SIZE_STACK (*pos_watches);
  const size_t neg_count = SIZE_STACK (*neg_watches);

  const uint64_t limit = pos_count + neg_count;
  uint64_t resolvents = 0;

  uint64_t ticks = 2;
  ticks += CACHE_LINES_OF_STACK (pos_watches);
  ticks += CACHE_LINES_OF_STACK (neg_watches);

  signed char *marks = solver->marks;

  assert (!solver->level);
  assert (!solver->values[pivot]);

  // Go over all clauses 'c' in which the variable occurs positively (outer
  // loop) and all clauses 'd' in which it occurs negative (inner loop) and
  // resolve 'c' with 'd' on the given variable.  Make sure to skip
  // satisfied clauses and tautological resolvents.  Save the resolvents on
  // the resolvents stack but eagerly add units (and the empty clause).

  for (all_elements_on_stack (union watch, pos_watch, *pos_watches))
    {
      struct clause *c = pos_watch.clause;
#ifndef NVIRTUAL
      if (is_tagged_clause (c))
	c = untag_clause (solver, 0, pivot, c);
      else
#endif
	{
	  ticks++;
	  if (c->garbage)
	    continue;
	}

      // Mark literals in 'c' to detect if a literal in 'c' occurs negated
      // in a 'd' clause which would produce a tautological resolvent.

      for (all_literals_in_clause (lit, c))
	mark_literal (marks, lit);

      for (all_elements_on_stack (union watch, neg_watch, *neg_watches))
	{
	  struct clause *d = neg_watch.clause;
#ifndef NVIRTUAL
	  if (is_tagged_clause (d))
	    d = untag_clause (solver, 1, not_pivot, d);
	  else
#endif
	    {
	      ticks++;
	      if (d->garbage)
		continue;
	    }

	  LOGCLS (c, "1st antecedent");
	  LOGCLS (d, "2nd antecedent");

	  INC (resolutions);

	  bool tautological = false;
	  for (all_literals_in_clause (lit, d))
	    if (lit != not_pivot && marked_literal (marks, lit) < 0)
	      {
		LOG ("tautological resolvent with clashing %s and %s",
		     LOGLIT (NOT (lit)), LOGLIT (lit));
		tautological = true;
		break;
	      }

	  if (tautological)
	    continue;

	  LOG ("resolvent non-tautological");

	  if (++resolvents > limit)
	    break;

	  // Copy literals of 'c' and 'd' to the resolvent stack skipping
	  // over the pivot and duplicated literals.

	  for (all_literals_in_clause (lit, c))
	    if (lit != pivot)
	      PUSH (solver->resolvents, lit);

	  for (all_literals_in_clause (lit, d))
	    if (!marks[INDEX (lit)])
	      PUSH (solver->resolvents, lit);

	  PUSH (solver->resolvents, INVALID);
	}

      for (all_literals_in_clause (lit, c))
	unmark_literal (marks, lit);

      if (resolvents > limit)
	break;

      if (solver->inconsistent)
	break;
    }

  ADD (elimination_ticks, ticks);

  if (solver->inconsistent)
    return false;

  if (resolvents > limit)
    {
      CLEAR_STACK (solver->resolvents);
      LOG ("many resolvents %" PRIu64 " > limit %" PRIu64, resolvents, limit);
      return false;
    }

  LOG ("few resolvents %" PRIu64 " <= limit %" PRIu64, resolvents, limit);
  return true;
}

// Add and connect the temporary resolvent clause.

static void
add_and_connect_resolvent (struct satch *solver)
{
  const size_t size = SIZE_STACK (solver->clause);
  assert (size <= UINT_MAX);

  if (!size)
    {
      LOG ("empty resolvent");
      solver->inconsistent = true;
    }
  else if (size == 1)
    {
      const unsigned unit = ACCESS (solver->clause, 0);
      LOG ("unit resolvent %s", LOGLIT (unit));
      assign (solver, unit, 0, true);
    }
#ifndef NVIRTUAL
  else if (size == 2)
    {
      const unsigned lit = ACCESS (solver->clause, 0);
      const unsigned other = ACCESS (solver->clause, 1);
      LOGBIN (false, lit, other, "resolvent");
      connect_literal (solver, lit, tag_binary_clause (false, other));
      connect_literal (solver, other, tag_binary_clause (false, lit));
      INC (irredundant);
    }
#endif
  else
    {
      struct clause *resolvent = new_irredundant_clause (solver);
      LOGCLS (resolvent, "resolvent");
      connect_clause (solver, resolvent);
    }

#ifndef NSUBSUMPTION

  // Mark variables in resolvent as subsumption candidates.

  for (all_elements_on_stack (unsigned, lit, solver->clause))
      mark_subsume_literal (solver, lit);

#endif
}

// Push the clause on the extension stack with 'eliminated' literal first.
// See 'extend_solution' for more explanations on why we need this.

static void
push_clause_on_extension_stack (struct satch *solver,
				unsigned eliminated, struct clause *c)
{
#ifndef NVIRTUAL
  if (is_tagged_clause (c))
    c = untag_clause (solver, 0, eliminated, c);
#endif
  PUSH (solver->extend, INVALID);	// Clause separator.
  PUSH (solver->extend, eliminated);
  for (all_literals_in_clause (lit, c))
    if (lit != eliminated)
      PUSH (solver->extend, lit);
}

static void
push_unit_on_extension_stack (struct satch *solver, unsigned eliminated)
{
  PUSH (solver->extend, INVALID);	// Clause separator.
  PUSH (solver->extend, eliminated);
}

static void
push_clauses_on_extension_stack (struct satch *solver,
				 unsigned eliminated, struct watches *watches)
{
  for (all_elements_on_stack (union watch, watch, *watches))
      push_clause_on_extension_stack (solver, eliminated, watch.clause);
}

// Eliminate clause and push it on extension stack with 'eliminated' first.

static void
eliminate_watched_clause (struct satch *solver,
			  unsigned eliminated, struct clause *c)
{
#ifndef NVIRTUAL
  if (is_tagged_clause (c))
    {
      const unsigned other = tagged_clause_to_literal (c);
      really_delete_binary (solver, false, eliminated, other);
      struct clause *d = tag_binary_clause (false, eliminated);
      disconnect_literal (solver, other, d);
      INC (elimination_ticks);
      c = untag_clause (solver, 0, eliminated, c);
    }
  else
#endif
  if (c->garbage)
    return;
#ifndef NVIRTUAL
  else
#endif
    mark_garbage (solver, c, "eliminated");

#ifdef NVIRTUAL
  (void) eliminated;
#endif
}

// Eliminate clauses with literal 'eliminated' by flushing their occurrence
// lists, marking them as garbage, and pushing them on the extension stack.

static void
eliminate_watched_clauses (struct satch *solver,
			   unsigned eliminated, struct watches *watches)
{
  for (all_elements_on_stack (union watch, watch, *watches))
      eliminate_watched_clause (solver, eliminated, watch.clause);
  RELEASE_STACK (*watches);
}

// Now eliminate the variable by adding all the saved resolvents from the
// resolvents stack and then eliminate the clauses in which it occurs.

// Since we might have generated units in the mean time we have to check for
// satisfied and falsified clauses again (the second time).

static void
eliminate_variable (struct satch *solver, unsigned pivot_idx)
{
  assert (!solver->inconsistent);
  assert (EMPTY_STACK (solver->clause));

  const unsigned pivot = LITERAL (pivot_idx);
  const unsigned not_pivot = NOT (pivot);

  LOG ("eliminating %s", LOGVAR (pivot_idx));

  // First mark the variable as eliminated and update counters.

  {
    struct flags *f = solver->flags + pivot_idx;
    assert (f->active);
    assert (!f->eliminated);
    f->eliminated = true;
    f->active = false;
    DEC (remaining);
    INC (eliminated);
  }

  // Now copy and add the clauses from the resolvents stack.

  uint64_t ticks = 0;

  {
    const signed char *const values = solver->values;
    bool satisfied = false;

    for (all_elements_on_stack (unsigned, lit, solver->resolvents))
      {
	if (lit != INVALID)
	  {
	    signed char value = values[lit];
	    if (value > 0)
	      satisfied = true;
	    else if (!satisfied && !value)
	      PUSH (solver->clause, lit);
	  }
	else if (satisfied)
	  {
	    CLEAR_STACK (solver->clause);
	    satisfied = false;
	  }
	else
	  {
	    LOGTMP ("previously resolved");
	    trace_and_check_temporary_addition (solver);
	    add_and_connect_resolvent (solver);
	    ticks += SIZE_STACK (solver->clause);
	    CLEAR_STACK (solver->clause);
	    ticks++;
	    if (solver->inconsistent)
	      break;
	  }
      }
  }

  if (solver->inconsistent)
    return;

  CLEAR_STACK (solver->resolvents);

  {
    struct watches *const pos_watches = solver->watches + pivot;
    struct watches *const neg_watches = solver->watches + not_pivot;

    const size_t pos_lines = 1 + CACHE_LINES_OF_STACK (pos_watches);
    const size_t neg_lines = 1 + CACHE_LINES_OF_STACK (neg_watches);

    // Push eliminated clauses on the extension stack.

#if 1
    // For non-incremental SAT solving we can push only one set of the two
    // clauses to the stack and simulate the other by pushing a unit.

    if (SIZE_STACK (*pos_watches) < SIZE_STACK (*neg_watches))
      {
	ticks += 1 + pos_lines;
	push_clauses_on_extension_stack (solver, pivot, pos_watches);
	push_unit_on_extension_stack (solver, not_pivot);
      }
    else
      {
	ticks += 1 + neg_lines;
	push_clauses_on_extension_stack (solver, not_pivot, neg_watches);
	push_unit_on_extension_stack (solver, pivot);
      }
#else
    // For incremental SAT solving we would need to save all clauses.

    push_clauses_on_extension_stack (solver, pivot, pos_watches);
    push_clauses_on_extension_stack (solver, not_pivot, neg_watches);
#endif

    // Finally remove all the clauses with the eliminated variables and
    // release their watcher stacks.

    ticks += 2 + pos_lines + neg_lines;

    eliminate_watched_clauses (solver, pivot, pos_watches);
    eliminate_watched_clauses (solver, not_pivot, neg_watches);
  }

  ADD (elimination_ticks, ticks);
}

/*------------------------------------------------------------------------*/

#ifndef NELIMINATIONLIMITS

// Variable elimination and particularly subsumption have to be bounded for
// large instances.  Otherwise almost all time is spent in these procedures.
// We bound the time spent by 'ticks' (predicted cache line accesses) as for
// propagation during search and allow a fixed fraction (10%) in terms of
// search ticks since the last variable elimination. We have separate limits
// for subsumption and elimination to allow each a fair share of the time.
// The limits are set at the start of variable elimination (for both).

static void
set_elimination_ticks_limit (struct satch *solver)
{
  struct limits *const limits = &solver->limits;
  const struct statistics *const statistics = &solver->statistics;
  const uint64_t eliminations = statistics->eliminations;
#ifndef NINPROCESSING
  const uint64_t delta = statistics->ticks - limits->eliminate.search;
  uint64_t limit = delta * elimination_ticks_fraction;
  message (solver, 2, "elimination", eliminations,
	   "elimination limit of %" PRIu64 " ticks = %g * search ticks %"
	   PRIu64, limit, (double) elimination_ticks_fraction, delta);
  limits->eliminate.ticks = statistics->elimination_ticks + limit;
#else
  limits->eliminate.ticks = UINT64_MAX;
  message (solver, 2, "elimination", eliminations,
	   "no elimination ticks-limit during preprocessing "
	   "(inprocessing disabled)");
#endif
}

static bool
elimination_ticks_limit_hit (struct satch *solver)
{
  return solver->statistics.elimination_ticks >
    solver->limits.eliminate.ticks;
}

#endif

#ifndef NSUBSUMPTIONLIMITS

static void
set_subsumption_ticks_limit (struct satch *solver)
{
  struct limits *const limits = &solver->limits;
  const struct statistics *const statistics = &solver->statistics;
  const uint64_t eliminations = statistics->eliminations;
#ifndef NINPROCESSING
  const uint64_t delta = statistics->ticks - limits->subsume.search;
  uint64_t limit = delta * subsumption_ticks_fraction;
  message (solver, 2, "elimination", eliminations,
	   "subsumption limit of %" PRIu64 " ticks = %g * search ticks %"
	   PRIu64, limit, (double) subsumption_ticks_fraction, delta);
  limits->subsume.ticks = statistics->subsumption_ticks + limit;
#else
  limits->subsume.ticks = UINT64_MAX;
  message (solver, 2, "elimination", eliminations,
	   "no subsumption ticks-limit during preprocessing "
	   "(inprocessing disabled)");
#endif
}

#endif

/*------------------------------------------------------------------------*/

// The main bounded variable elimination function.

static int
eliminate_variables (struct satch *solver)
{
  START (eliminate);
  const uint64_t eliminations = INC (eliminations);

  // First backtrack to decision level zero.

  update_phases_and_backtrack_to_root_level (solver);
  assert (solver->trail.propagate == solver->trail.end);

#ifndef NELIMINATIONLIMITS
  set_elimination_ticks_limit (solver);
#endif
#ifndef NSUBSUMPTIONLIMITS
  set_subsumption_ticks_limit (solver);
#endif

  // Switch to dense mode which flushes all watches to redundant clauses and
  // connects all occurrences of literals in irredundant clauses.

  switch_to_dense_mode (solver);

  // Main elimination loop.

  unsigned eliminated, total = 0, round = 0;
  const unsigned original = solver->statistics.remaining;

  do
    {
#ifndef NSUBSUMPTION
      full_backward_subsumption (solver);
      if (!more_elimination_candidates (solver))
	break;
#endif
      const unsigned remaining = solver->statistics.remaining;
      eliminated = 0;
      round++;

      for (all_variables (idx))
	{
	  if (can_be_eliminated (solver, idx) &&	// Check limits.
	      produces_few_resolvents (solver, idx))	// Save resolvents.
	    {
	      eliminate_variable (solver, idx);	// Add resolvents.
	      eliminated++;
	    }
	  else
	    solver->flags[idx].eliminate = false;

	  if (solver->inconsistent)
	    break;

#ifndef NELIMINATIONLIMITS
	  if (elimination_ticks_limit_hit (solver))
	    {
	      message (solver, 4, "elimination", eliminations,
		       "elimination ticks limit hit");
	      break;
	    }
#endif
	}

      total += eliminated;
      message (solver, 3, "elimination", eliminations,
	       "eliminated %u variables %.0f%% of remaining %u in round %u",
	       eliminated, percent (eliminated, remaining), remaining, round);

      report (solver, 1 + !eliminated, 'e');
#ifndef NELIMINATIONLIMITS
      if (round >= elimination_rounds)
	break;
      if (elimination_ticks_limit_hit (solver))
	break;
#endif
    }
  while (!solver->inconsistent && eliminated);

  unsigned kept = 0;
  const struct flags *const flags = solver->flags;
  for (all_variables (idx))
    {
      const struct flags *const f = flags + idx;
      if (!f->active)
	continue;
      if (f->eliminate)
	kept++;
    }

  message (solver, 3, "elimination", eliminations,
	   "keeping %u variables scheduled %.0f%%",
	   kept, percent (kept, solver->statistics.remaining));

  message (solver, 2, "elimination", eliminations,
	   "eliminated %u variables %.0f%% in total in %u rounds",
	   total, percent (total, original), round);

  // Collect clauses which are marked garbage, i.e., are root-level
  // satisfied or contain an eliminated variable.

  mark_and_collect_garbage_clauses_after_elimination (solver);

  // Switch back to sparse mode watching all clauses.

  switch_to_sparse_mode (solver);

  // Need to propagate over redundant clauses too.

  solver->trail.propagate = solver->trail.begin;

#ifndef NINPROCESSING

  // Finally update limits.

  {
    const struct statistics *const statistics = &solver->statistics;
    struct limits *const limits = &solver->limits;

    if (!kept)
      {
	limits->eliminate.fixed = statistics->fixed;
	limits->eliminate.marked = statistics->marked_eliminate;
      }

#ifndef NELIMINATIONLIMITS
    limits->eliminate.search = statistics->ticks;
#endif
#ifndef NSUBSUMPTIONLIMITS
    limits->subsume.search = statistics->ticks;
#endif

    const uint64_t interval =
      scale_interval (elimination_interval, nlognlogn, eliminations);
    limits->eliminate.conflicts = CONFLICTS + interval;

    message (solver, 4, "elimination", eliminations,
	     "next limit at %" PRIu64 " after %" PRIu64 " conflicts",
	     limits->eliminate.conflicts, interval);
  }
#endif

  STOP (eliminate);

  return solver->inconsistent ? 20 : 0;
}

static void
extend_solution (struct satch *solver)
{
  const unsigned *const begin = solver->extend.begin;
  signed char *const values = solver->values;

  const unsigned *p = solver->extend.end;

  unsigned last = INVALID;
  bool satisfied = false;
  signed char value = -1;

  while (p != begin)
    {
      const unsigned lit = *--p;
      if (lit != INVALID)
	{
	  value = values[lit];
	  assert (value);
	  if (value > 0)
	    satisfied = true;
	}
      else if (!satisfied)
	{
	  assert (last != INVALID);
	  values[last] = 1;
	  values[NOT (last)] = -1;
	  LOG ("flipped value of %s", LOGLIT (last));
	}
      else
	satisfied = false;
      last = lit;
    }
}

/*------------------------------------------------------------------------*/
#endif // of '#ifndef NELIMINATION'
/*------------------------------------------------------------------------*/
