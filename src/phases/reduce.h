/*------------------------------------------------------------------------*/

// Reducing the clause data base by removing useless redundant clauses is
// important to keep the memory usage of the solver low, but also to
// speed-up propagation.  The reduction interval in terms of conflicts is
// increased (almost) arithmetically by 'reduce_interval'.  We combine
// reductions with clause data base simplifications which remove root-level
// satisfied clauses.  Removing falsified literals is not implemented yet.

#ifndef NREDUCE

static bool
reducing (struct satch *solver)
{
  return solver->limits.reduce.conflicts <= CONFLICTS;
}

// Protect reason clauses from garbage collection. The same function can
// be used afterwards to make reason clauses unprotected again.  It is
// better to lazily protect clauses during reductions instead of eagerly
// setting the 'protect' bit during assignments to avoid dereferencing
// pointers to binary clause reasons (if 'NBLOCK' is defined).

static void
set_protect_flag_of_reasons (struct satch *solver, bool protect)
{
  struct clause *const *const reasons = solver->reasons;
  for (all_elements_on_stack (unsigned, lit, solver->trail))
    {
      const unsigned idx = INDEX (lit);
      struct clause *reason = reasons[idx];
      if (!reason)
	continue;
#ifndef NBLOCK
      if (is_tagged_clause (reason))
	continue;
#endif
      LOGCLS (reason, "%sprotecting", protect ? "" : "un");
      assert (reason->protected != protect);
      reason->protected = protect;
    }
}

#endif

#if !defined(NREDUCE) || !defined(NELIMINATION)

// Check whether a clause is root-level satisfied, i.e., it contains a
// literal which is assigned to true on decision-level zero.  Otherwise
// flush (at least) virtually all root-level falsified literals.  The latter
// is important for marking flushed literals as new subsume candidates.

static bool
clause_satisfied (struct satch *solver, struct clause *c)
{
  assert (!solver->level);
#ifndef NVIRTUAL
  assert (!is_tagged_clause (c));
  assert (!is_temporary_binary (solver, c));
  assert (!c->protected);
#endif

  const signed char *const values = solver->values;
  unsigned num_false = 0;

  for (all_literals_in_clause (lit, c))
    {
      const signed char value = values[lit];
      if (value > 0)
	return true;
      if (value < 0)
	num_false++;
    }

  if (!num_false)
    return false;

  LOGCLS (c, "found %u root-level falsified in", num_false);

  assert (EMPTY_STACK (solver->clause));
  for (all_literals_in_clause (lit, c))
    if (!values[lit])
      PUSH (solver->clause, lit);

#ifndef NSUBSUMPTION
  for (all_elements_on_stack (unsigned, lit, solver->clause))
      mark_subsume_literal (solver, lit);
#endif

  if (!solver->dense)
    {
      trace_and_check_temporary_addition (solver);
      trace_and_check_clause_deletion (solver, c);

#ifndef NWATCHES
      const unsigned *old_lits = c->literals;
      const unsigned *new_lits = solver->clause.begin;

      // Unwatching might break code where we traverse watchers, which is
      // currently only the case when called in dense mode from
      // 'actual_number_of_occurrences' and thus not reached.

      unwatch_literal (solver, old_lits[0], c);
      unwatch_literal (solver, old_lits[1], c);
#else
      for (all_literals_in_clause (lit, c))
	disconnect_literal (solver, lit, c);
#endif

      const size_t size = SIZE_STACK (solver->clause);
      assert (size == c->size - num_false);
      assert (size >= 2);

      // We can not simply add a new clause since this function is called
      // while traversing the 'irredundant' or 'redundant' stacks.  Instead
      // we disconnect and add new watches.  Partially keeping unassigned
      // watches is possible but needs more complex code (it might also
      // result in blocking literals not in the clause anymore).

#ifndef NVIRTUAL
      if (size == 2)
	{
	  watch_binary (solver, c->redundant, new_lits[0], new_lits[1]);
	  watch_binary (solver, c->redundant, new_lits[1], new_lits[0]);
	  LOGCLS (c, "garbage after flushing %u literals", num_false);
	  c->garbage = true;
	}
      else
#endif
	{
#ifndef NWATCHES
#ifndef NBLOCK
	  watch_literal (solver, c->redundant, new_lits[0], new_lits[1], c);
	  watch_literal (solver, c->redundant, new_lits[1], new_lits[0], c);
#else
	  watch_literal (solver, new_lits[0], c);
	  watch_literal (solver, new_lits[1], c);
#endif
#endif
	  unsigned *p = c->literals;
	  for (all_elements_on_stack (unsigned, lit, solver->clause))
	     *p++ = lit;

	  c->size = size;
#ifndef NGLUE
	  if (c->redundant && c->size >= c->glue)
	    c->glue = size - 1;
#endif
#ifndef NCACHE
	  c->search = 0;
#endif
#ifdef NWATCHES
	  connect_clause (solver, c);
	  count_clause (solver, c);
#endif
	  LOGCLS (c, "flushing %u literals yields", num_false);
	}

      // But there is no need to update clause statistics.
    }

  CLEAR_STACK (solver->clause);

  return false;
}

// This function is called in default sparse mode from 'reduce' only and
// then (through 'clause_satisfied') also flushes falsified literals.  In
// dense mode it is only called from 'actual_number_of_occurrences' during
// variable elimination attempts.  There it only updates 'subsume'
// candidates if the clause is not garbage but contains falsified literals.

static bool
mark_garbage_if_satisfied (struct satch *solver, struct clause *c)
{
  assert (!solver->level);
#ifndef NVIRTUAL
  assert (!is_tagged_clause (c));
  assert (!is_temporary_binary (solver, c));
#endif
  if (c->garbage)
    return true;
  if (!clause_satisfied (solver, c))
    return false;
  mark_garbage (solver, c, "root-level satisfied");
  return true;
}

// Irredundant clauses are not reduced, but marked garbage if they are
// root-level satisfied clauses and can then be collected during reduction
// too.  This is only necessary if there are new root-level fixed variables
// since the last reduction though (and restricted to unprotected clauses).

// We also use this function after variable elimination since we might not
// have found and marked all the satisfied clauses during elimination.

// For subsumption an important side-effect of this function is to mark
// unassigned literals in not-satisfied irredundant clauses which contain
// false literals too as subsumption candidates.

static void
mark_irredundant_clauses_as_garbage_if_satisfied (struct satch *solver)
{
  assert (!solver->level);
  for (all_irredundant_clauses (c))
    (void) mark_garbage_if_satisfied (solver, c);
}

#endif

#ifndef NREDUCE

// Redundant clauses with large enough glucose level (glue) which have not
// been used since the last reduction are deletion candidates. If there
// are new root-level fixed variables since the last reduction we also
// mark clauses as garbage which are root-level satisfied.

static void
gather_reduce_candidates (struct satch *solver, bool new_fixed,
			  struct clauses *candidates)
{
  // Reverse order is needed for radix sort to ensure that more recently
  // learned clauses are kept if they have the same size and glue.

  // Without radix sort we need to use clause id's as tie-breaker anyhow and
  // thus reversing the redundant clauses on the candidates stack is not
  // necessary but also not harmful.

  for (all_redundant_clauses_in_reverse (c))
    {
      assert (c->redundant);
      if (c->garbage)
	continue;
      if (c->protected)
	continue;
      if (new_fixed)
	{
	  if (mark_garbage_if_satisfied (solver, c))
	    continue;
	  if (c->garbage)
	    continue;
	}
#ifndef NVIRTUAL
      assert (c->size > 2);
#else
      // As we can not protect binary reason clauses we just ignore them as.
      assert (c->size > 1);
      if (c->size == 2)
	continue;
#endif
#ifndef NTIER1
      if (c->glue <= tier1_glue_limit)
	continue;
#endif
#ifndef NUSED
      if (c->used)
	{
	  c->used--;		// Works for both 'used:1' and 'used:2'.
#ifndef NTIER2
	  if (c->glue <= tier2_glue_limit)
#endif
	    continue;
	}
#endif
      PUSH (*candidates, c);
    }

  if (solver->options.verbose < 2)
    return;

  const size_t size_candidates = SIZE_STACK (*candidates);
  const size_t redundant = SIZE_STACK (solver->redundant);
  message (solver, 2, "reduce", solver->statistics.reductions,
	   "gathered %zu reduce candidate clauses %.0f%%",
	   size_candidates, percent (size_candidates, redundant));
}

// Before actually deleting the garbage clauses we have to flush of course
// watches from the watcher lists pointing to such garbage clauses.

static void
flush_garbage_watches (struct satch *solver)
{
  struct watches *all_watches = solver->watches;
#ifndef NVIRTUAL
  signed char *const values = solver->values;
  const unsigned *const levels = solver->levels;
#endif
  for (all_literals (lit))
    {
#ifndef NVIRTUAL
      signed char lit_value = values[lit];
      if (lit_value && levels[INDEX (lit)])
	lit_value = 0;
#endif
      struct watches *const lit_watches = all_watches + lit;
      union watch *const end = lit_watches->end;
      union watch *q = lit_watches->begin;
      const union watch *p = q;
      while (p != end)
	{
#ifndef NBLOCK
	  const union watch watch = *p++;
#ifndef NVIRTUAL
	  const struct header header = watch.header;
	  if (header.binary)
	    {
	      const unsigned blocking = header.blocking;

	      signed char blocking_value = values[blocking];
	      if (blocking_value && levels[INDEX (blocking)])
		blocking_value = 0;

	      // We want to eagerly remove root-level satisfied binary
	      // clauses as well, but since those sit in watch lists only
	      // (if 'NVIRTUAL' and 'NBLOCK' are undefined) we have to check
	      // whether the literal or the other blocking literal are
	      // root-level assigned.  In both cases (since we assume
	      // propagation went to completion on the root-level) we know
	      // that the binary clause has to be satisfied.

	      if (lit_value || blocking_value)
		{
		  assert (lit_value > 0 || blocking_value > 0);
		  delete_binary (solver, header.redundant, lit, blocking);
		  continue;	// Drop header by not copying it.
		}
	      *q++ = watch;	// Keep header and skip non-existing clause.
	      continue;
	    }
#endif
	  *q++ = watch;		// Keep blocking literal header.
#endif
	  const struct clause *const clause = (*q++ = *p++).clause;
	  if (clause->garbage)
	    q -= long_clause_watch_size;	// Stop watching clause.
	}
      lit_watches->end = q;
    }
}

#endif

#if !defined(NREDUCE) || !defined(NELIMINATION)

// After removing garbage watches we can finally delete garbage clauses.

static void
delete_garbage_clauses (struct satch *solver, struct clauses *clauses,
			size_t *bytes_ptr, size_t *count_ptr)
{
  size_t bytes = 0;
  size_t count = 0;

  struct clause *const *const end = clauses->end;
  struct clause **q = clauses->begin;

  for (struct clause ** p = q; p != end; p++)
    {
      struct clause *const c = *p;
      if (c->garbage)
	{
	  assert (!c->protected);
	  bytes += delete_clause (solver, c);
	  count++;
	}
      else
	*q++ = c;
    }
  clauses->end = q;

  *bytes_ptr += bytes;
  *count_ptr += count;
}

#endif

#ifndef NREDUCE

/*------------------------------------------------------------------------*/

// Candidate clauses considered to be reduced are sorted with respect to
// their potential usefulness in the future.  Clauses are considered more
// useful if they have a smaller glue or smaller size with the same glue.
// If both glue and size are the same we keep more recently learned clauses.

#ifndef NRADIXSORT

#ifndef NGLUE

static uint64_t
rank_clause (struct clause *c)
{
  return ((uint64_t) c->glue << 32) + c->size;
}

static void
sort_reduce_candidates (struct clauses *candidates)
{
  RSORT (struct clause *, uint64_t, *candidates, rank_clause);
}

#else

static unsigned
rank_clause (struct clause *c)
{
  return c->size;
}

static void
sort_reduce_candidates (struct clauses *candidates)
{
  RSORT (struct clause *, unsigned, *candidates, rank_clause);
}

#endif

#else

// This the actual comparison functions for 'qsort' to order reduce
// candidates.  The result is negative if the first argument is more useful
// than the second.  The result is positive, if the second argument is more
// useful.  Since 'qsort is not stable we make comparison deterministic by
// using clause id's as tie-breaker which also makes sure that more recently
// learned clauses are considered to be more useful in the future if they
// happen to have the same glue and size.

static int
cmp_reduce (const void *p, const void *q)
{
  const struct clause *const c = *(const struct clause * const *) p;
  const struct clause *const d = *(const struct clause * const *) q;
#ifndef NGLUE
  if (c->glue < d->glue)
    return -1;
  if (c->glue > d->glue)
    return 1;
#endif
  if (c->size < d->size)
    return -1;
  if (c->size > d->size)
    return 1;
  if (c->id < d->id)
    return 1;
  assert (c->id > d->id);
  return -1;
}

static void
sort_reduce_candidates (struct clauses *candidates)
{
  struct clause **begin = candidates->begin;
  qsort (begin, SIZE_STACK (*candidates), sizeof *begin, cmp_reduce);
}

#endif

/*------------------------------------------------------------------------*/

// From the remaining candidates we reduce 'reduce_fraction' of clauses.

static void
mark_garbage_candidates (struct satch *solver, struct clauses *candidates)
{
  const size_t size = SIZE_STACK (*candidates);
  assert (0.0 <= reduce_fraction);
  const size_t reduce = reduce_fraction * size;

  message (solver, 4, "reduce", solver->statistics.reductions,
	   "target is to reduce %zu out of %zu clauses %.0f%%",
	   reduce, size, percent (reduce, size));

  const double keep_fraction = 1.0 - reduce_fraction;
  const size_t keep = keep_fraction * size;

  size_t reduced = 0;

  while (SIZE_STACK (*candidates) > keep)
    {
      struct clause *c = POP (*candidates);
      assert (!c->protected);
      mark_garbage (solver, c, "reducing");
      reduced++;
    }

  ADD (reduced, reduced);

  message (solver, 3, "reduce", solver->statistics.reductions,
	   "reducing %zu out of %zu clauses %.0f%%",
	   reduced, size, percent (reduced, size));

}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG

// Even though the 'irredundant' and 'redundant' clause statistics are only
// used for reporting we still want to accurately measure and maintain them,
// which unfortunately is not trivial.  These reports are very useful for
// engineering heuristics (and sometimes debugging).

// Thus we perform this explicit check before and after 'reduce'.

static void
check_clause_statistics (struct satch *solver)
{
  assert (!solver->dense);

  uint64_t irredundant = 0;
  uint64_t redundant = 0;

#ifndef NVIRTUAL
  for (all_literals (lit))
    {
      const struct watches *const watches = solver->watches + lit;
      const union watch *const end = watches->end;
      const union watch *p = watches->begin;
      while (p != end)
	{
	  const union watch watch = *p++;
	  const struct header header = watch.header;
	  if (header.binary)
	    {
	      const unsigned other = header.blocking;
	      if (lit < other)
		{
		  if (header.redundant)
		    redundant++;
		  else
		    irredundant++;
		}
	    }
	  else
	    p++;
	}
    }
#endif

  for (all_irredundant_clauses (c))
    if (!c->garbage)
      irredundant++;

  for (all_redundant_clauses (c))
    if (!c->garbage)
      redundant++;

  assert (irredundant == solver->statistics.irredundant);
  assert (redundant == solver->statistics.redundant);
}

#endif

/*------------------------------------------------------------------------*/

// Reduce less useful redundant clauses frequently.

static void
reduce (struct satch *solver)
{
#ifndef NDEBUG
  check_clause_statistics (solver);
#endif
  START (reduce);
  const uint64_t reductions = INC (reductions);

  // If there are new fixed (root-level assigned) variables since the last
  // reduction, we remove both satisfied irredundant clauses here and later
  // satisfied redundant clauses in 'gather_reduce_candidates'.  Both call
  // 'mark_garbage_if_satisfied' for large clauses, which in turn calls
  // 'clause_satisfied' and thus also flushes falsified literals.

  // Without new fixed variable we do not backtrack but protect reasons.

  const bool new_fixed =
    solver->limits.reduce.fixed < solver->statistics.fixed;

  if (new_fixed)
    {
      update_phases_and_backtrack_to_root_level (solver);
      mark_irredundant_clauses_as_garbage_if_satisfied (solver);
    }
  else
    set_protect_flag_of_reasons (solver, true);

  // At the core of reduction is to first gather potential redundant reduce
  // candidate clauses (omitting those that are definitely kept).  Then
  // these candidates are sorted with respect to a metric which is supposed
  // to reflect potential usefulness. From the less useful clauses a large
  // fraction ('reduce_fraction') is then marked as garbage to be collected.

  {
    struct clauses candidates;
    INIT_STACK (candidates);

    gather_reduce_candidates (solver, new_fixed, &candidates);
    sort_reduce_candidates (&candidates);
    mark_garbage_candidates (solver, &candidates);

    RELEASE_STACK (candidates);
  }

  // Before we can delete the garbage clauses we first have to remove
  // references to those clauses marked as garbage from the watch lists.

  flush_garbage_watches (solver);

  // As next to final step we delete garbage clauses and print statistics.

  {
    size_t bytes = 0, count = 0;
    if (new_fixed)
      delete_garbage_clauses (solver, &solver->irredundant, &bytes, &count);
    delete_garbage_clauses (solver, &solver->redundant, &bytes, &count);

    // We report on how many clauses we collected during reduction.

    message (solver, 2, "reduce", reductions,
	     "collected %zu clauses (%zu bytes, %.0f MB)",
	     count, bytes, bytes / (double) (1u << 20));

    ADD (collected, bytes);
  }

  // No we can mark reasons of literals on the trail as unprotected.

  if (!new_fixed)
    set_protect_flag_of_reasons (solver, false);

  // Finally we compute and report the next conflict limit for reduction.

  {
    solver->limits.reduce.fixed = solver->statistics.fixed;
    const uint64_t interval =
      scale_interval (reduce_interval, ndivlogn, reductions);
    solver->limits.reduce.conflicts = CONFLICTS + interval;
    message (solver, 4, "reduce", reductions,
	     "next limit at %" PRIu64 " after %" PRIu64 " conflicts",
	     solver->limits.reduce.conflicts, interval);
  }

  report (solver, 1, '-');
  STOP (reduce);
#ifndef NDEBUG
  check_clause_statistics (solver);
#endif
}

#endif

