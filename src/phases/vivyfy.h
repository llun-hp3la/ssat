#ifndef NVIVIFICATION

static signed char
satch_fixed (struct satch *solver, unsigned lit)
{

  assert (lit < LITERALS);
  const signed char value = solver->values[lit];
  if (!value)
    return 0;
  if (solver->levels[INDEX (lit)])
    return 0;
  return value;
}

static inline int
int_compare (long int a, long int b)
{
  if (a < b)
    return -1;
  if (a == b)
    return 0;
  return 1;
}

#ifdef NRADIXSORT

static inline int
more_occurrences (const void *cp, const void *dp, void *countsp)
  {
      unsigned *counts = (unsigned *) countsp;
      const unsigned litA = *((unsigned*) cp);
      const unsigned litB = *((unsigned*) dp);
      return int_compare (counts[litA], counts[litB]);
  }

#endif

static void
vivify_sort_lits_by_counts (struct satch *solver, unsigned *counts,
			    struct unsigned_stack *c)
{

#ifndef NRADIXSORT
  (void) solver;
#define MORE_OCCURRENCES(LIT) \
  ~counts[LIT]

  RSORT (unsigned, unsigned, *c, MORE_OCCURRENCES);
#else

#define MORE_OCCURRENCES(LITA,LITB) \
  ((~counts[LITA]) < (~counts[LITB]))
  SORT_STACK (unsigned, *c, MORE_OCCURRENCES);
#endif
}

static void
vivify_sort_stack_by_counts (struct satch *solver, unsigned *counts,
			     struct unsigned_stack *c)
{
  vivify_sort_lits_by_counts (solver, counts, c);
}

static void
vivify_sort_clause_by_counts (struct satch *solver, unsigned *counts,
			      struct clause *c)
{
#ifndef NBLOCK
  assert (!is_tagged_clause (c));
#endif
#ifndef NVIRTUAL
  assert (!is_temporary_binary (solver, c));
#endif
  struct unsigned_stack c2 = {.begin = c->literals,
    .end = c->literals + c->size,
    .allocated = c->literals + c->size
  };
  vivify_sort_lits_by_counts (solver, counts, &c2);
}


static inline bool
worse_candidate (unsigned* counts, const struct clause *const c, const struct clause *const d)
{
  assert (c);
  assert (d);
  assert (counts);
#ifndef NBLOCK
  assert (!is_tagged_clause (c));
  assert (!is_tagged_clause (d));
#endif
  if (!c->vivify && d->vivify)
    return true;

  if (c->vivify && !d->vivify)
    return false;

  unsigned const *p = c->literals;
  unsigned const *q = d->literals;
  const unsigned *const e = c->literals + c->size;
  const unsigned *const f = d->literals + d->size;

  while (p != e && q != f)
    {
      const unsigned a = *p++;
      const unsigned b = *q++;
      if (a == b)
	continue;
      const unsigned u = counts[a];
      const unsigned v = counts[b];
      if (u < v)
        return true;
      if (u > v)
        return false;
      return a < b;
    }

  if (p != e && q == f)
    return true;
  if (p == e && q != f)
    return false;

  return (long int)c < (long int)d;
}


static void
sort_vivification_candidates (struct satch *solver,
			      struct clauses *schedule, unsigned *counts)
{
  for (all_pointers_on_stack (struct clause, c, *schedule))
    {
      vivify_sort_clause_by_counts (solver, counts, c);
    }
#define WORSE_CANDIDATE(c, d) \
  worse_candidate (counts, c, d)

  SORT_STACK (struct clause*, *schedule, WORSE_CANDIDATE);
}

static void
count_literal (unsigned lit, unsigned *counts)
{
  const unsigned old_count = counts[lit];
  const unsigned new_count =
    (old_count < UINT_MAX) ? old_count + 1 : UINT_MAX;
  counts[lit] = new_count;
}

static void
vivify_count_clause (struct clause *c, unsigned *counts)
{
  for (all_literals_in_clause (lit, c))
    count_literal (lit, counts);
}

void
flush_large_watches (struct satch *solver)
{
#ifdef NWATCHES
  (void)solver;
#else
  LOG ("flush large clause watches");
  struct watches *all_watches = solver->watches;
  for (all_literals (lit))
    {
      struct watches *lit_watches = all_watches + lit;
#ifndef NBLOCK
      union watch *q = lit_watches->begin;
      const union watch *const end = lit_watches->end, *p = q;
      while (p != end)
	{
	  const union watch watch = *q++ = *p++;	// Keep header by default.
	  const struct header header = watch.header;
	  if (header.binary)
	    {
#ifdef NVIRTUAL
	      *q++ = *p++;	// Copy clause too.
#endif
	    }
	  else
	    {
	      q--;		// don't keep clause
	      p++;
	    }
	}
      lit_watches->end = q;
#else
      lit_watches->end = lit_watches->begin;
#endif
    }
#endif
#ifndef NDEBUG
  solver->watching = false;
#endif
}

void
watch_large_clauses (struct satch *solver)
{
  LOG ("rewatch large clause watches");
  for (all_irredundant_clauses (c))
    {
      if (c->garbage)
	continue;
#ifndef NCACHE
      c->search = 0;
#endif
#ifndef NWATCHES
      watch_clause (solver, c);
#endif
    }
  for (all_redundant_clauses (c))
    {
      if (c->garbage)
	continue;
#ifndef NCACHE
      c->search = 0;
#endif
#ifndef NWATCHES
      watch_clause (solver, c);
#endif
    }
#ifndef NDEBUG
  solver->watching = true;
#endif
}

static void
promote_clause (struct satch *solver, struct clause *c, unsigned glue)
{
#ifdef NGLUE
  (void) solver;
  (void) c;
  (void) glue;
  return;
#else
#ifndef NTIER1
  const unsigned old_glue = c->glue;
  assert (old_glue >= c->glue);

  c->glue = glue;
  if (old_glue > tier1_glue_limit && glue <= tier1_glue_limit)
    {
      LOGCLS (c, "promoting to TIER1");
    }
#ifndef NTIER2
  else if (old_glue > tier2_glue_limit && glue <= tier2_glue_limit)
    {
      LOGCLS (c, "promoting to TIER2");
#ifndef NUSED
      c->used = 2;
#endif
    }
  else
    {
      LOGCLS (c, "keeping to new glue %u in tier3", glue);
    }
#endif
#else
  (void) solver;
  c->glue = glue;
#endif
#endif
}

// The function marked_literal cannot be used for vivification because it only marks variables
// instead of literals despite the name (!).
inline static signed char
vivify_marked_literal (struct satch *solver, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  signed char res = solver->vivify_marks[idx];
  return (res == INT_SIGN (lit));
}

void
vivify_mark_literal (struct satch *solver, unsigned lit)
{

  const unsigned idx = INDEX (lit);
  assert (!solver->vivify_marks[idx]);
  solver->vivify_marks[idx] = INT_SIGN (lit);
}

static struct clause *
vivify_boolean_constraint_propagation (struct satch *solver,
				       struct clause *ignore)
{
  struct trail *trail = &solver->trail;
  unsigned *propagate = trail->propagate;
  unsigned *p;

  assert (trail->begin <= propagate);
  assert (propagate <= trail->begin + VARIABLES);

  struct clause *conflict = 0;
  uint64_t ticks = 0;

  if (ignore)
    LOGCLS (ignore, "vivify: BCP ignoring");
  for (p = propagate; !conflict && p != trail->end; p++)
    conflict = propagate_literal (solver, *p, ignore, &ticks);

  ADD (probing_ticks, ticks);
  solver->trail.propagate = p;
  const unsigned propagated = p - propagate;

  ADD (vivify_propagations, propagated);

  if (conflict)
    INC (vivify_conflicts);

  return conflict;
}

static void
vivify_binary_or_large_conflict (struct satch *solver,
				 struct clause *conflict)
{
  assert (solver->level);
  assert (conflict->size >= 2);
  LOGCLS (conflict, "vivify analyzing conflict (red: %d)",
	  conflict->redundant);
#if LOGGING || !defined(NDEBUG)
  unsigned conflict_level = 0;
#endif
  for (all_literals_in_clause (lit, conflict))
    {
      assert (solver->values[lit] < 0);
      const unsigned level = solver->levels[INDEX (lit)];
      if (!level)
	continue;
#if LOGGING || !defined(NDEBUG)
      if (level > conflict_level)
	conflict_level = level;
#endif
      mark_analyzed (solver, INDEX (lit));
    }
  LOG ("vivify conflict level %u", conflict_level);
  assert (0 < conflict_level);
  assert (conflict_level == solver->level);
}

static void
vivify_mark_garbage (struct satch *solver, struct clause *c, const char *msg)
{
  assert (solver->watching);
#ifndef NWATCHES
  unwatch_literal (solver, c->literals[0], c);
  unwatch_literal (solver, c->literals[1], c);
#else
  for (all_literals_in_clause (lit, c))
    disconnect_literal (solver, lit, c);
#endif
  mark_garbage (solver, c, msg);
}

static bool
vivify_learn (struct satch *solver,
	      struct clause *c,
	      unsigned non_false, bool irredundant, unsigned implied)
{
  bool res;

  size_t size = SIZE_STACK (solver->clause);
  assert (size <= non_false);
  assert (2 < non_false);

  if (size == 1)
    {
      LOG ("size 1 learned unit clause forces jump level 0");
      if (solver->level)
	backtrack (solver, 0);

      const unsigned unit = ACCESS (solver->clause, 0);
      assign (solver, unit, 0, true);
      solver->iterate = true;
      vivify_mark_garbage (solver, c, "subsumed by unit");
      assert (!solver->level);
      struct clause *conflict = boolean_constraint_propagation (solver);
      if (conflict)
	{
	  assert (solver->level == 0);
	  LOGCLS (conflict, "found conflict at level 0");
	  solver->inconsistent = true;
	  return false;
	}
      INC (vivify_strengthened);
      res = true;
    }
  else
    {
      const unsigned *const levels = solver->levels;
      const signed char *const values = solver->values;

      unsigned highest_level = 0;
      for (all_elements_on_stack (unsigned, lit, solver->clause))
	{
	  const signed char value = values[lit];
	  if (!value)
	    {
	      LOG ("unassigned literal %s in learned clause", LOGLIT (lit));
	      highest_level = INVALID_LEVEL;
	      break;
	    }
	  const unsigned idx = INDEX (lit);
	  const unsigned level = levels[idx];
	  assert (level > 0);
	  if (level > highest_level)
	    highest_level = level;
	}

      if (highest_level != INVALID_LEVEL)
	LOG ("highest level %u in learned clause", highest_level);

      unsigned literals_on_highest_level = 0;
      for (all_elements_on_stack (unsigned, lit, solver->clause))
	{
	  const unsigned value = values[lit];
	  if (!value)
	    literals_on_highest_level++;
	  else
	    {
	      const unsigned idx = INDEX (lit);
	      const unsigned level = levels[idx];
	      assert (level > 0);
	      if (level == highest_level)
		literals_on_highest_level++;
	    }
	}
#ifdef LOGGING
      if (highest_level == INVALID_LEVEL)
	LOG ("found %u unassigned literals", literals_on_highest_level);
      else
	LOG ("found %u literals on highest level", literals_on_highest_level);
#endif
      if (highest_level == INVALID_LEVEL && literals_on_highest_level > 1)
	LOG ("no need to backtrack with more than one unassigned literal");
      else
	{
	  unsigned jump_level = 0;
	  for (all_elements_on_stack (unsigned, lit, solver->clause))
	    {
	      const signed char value = values[lit];
	      if (!value)
		continue;
	      const unsigned idx = INDEX (lit);
	      const unsigned level = levels[idx];
	      if (level == highest_level)
		continue;
	      if (level > jump_level)
		jump_level = level;
	    }
	  LOG ("determined jump level %u", jump_level);

	  if (jump_level < solver->level)
	    backtrack (solver, jump_level);
	}

#ifndef NVIRTUAL
      if (size == 2)
	{
#ifdef LOGGING
	  const unsigned lit = ACCESS (solver->clause, 0);
	  const unsigned other = ACCESS (solver->clause, 1);
#endif
	  const bool redundant = c->redundant;
	  LOGBIN (false, lit, other, "vivification");
	  trace_and_check_temporary_addition (solver);
	  add_new_binary_and_watch_it (solver, redundant);

	  vivify_mark_garbage (solver, c, "vivified clause");
	  INC (vivify_strengthened);
	  res = true;
	}
      else
#endif
      if (size < non_false)
	{
#ifndef NVIRTUAL
	  assert (size > 2);
#else
	  assert (size >= 2);
#endif
	  CLEAR_STACK (solver->clause);
	  assert (EMPTY_STACK (solver->clause));
	  const unsigned old_size = c->size;
	  unsigned new_size = 0, *lits = c->literals;
#ifndef NWATCHES
	  const unsigned litA = lits[0];
	  const unsigned litB = lits[1];
#endif

	  assert (EMPTY_STACK (solver->clause));
	  for (unsigned i = 0; i < old_size; i++)
	    {
	      const unsigned lit = lits[i];
	      assert (lit < LITERALS);
	      PUSH (solver->clause, lit);
	      bool keep = true;
	      if (lit != implied)
		{
		  const unsigned idx = INDEX (lit);
		  const signed char mark = solver->marks[idx];
		  if (!(mark & ANALYZED))
		    keep = false;
		  else if (solver->reasons[idx])
		    keep = false;
		  if (!keep)
		    LOG
		      ("literal %s not to be kept (has reason? %d; not analyzed? %d)",
		       LOGLIT (lit), solver->reasons[idx] ? 1 : 0,
		       !(mark & ANALYZED) ? 1 : 0);
		}
	      if (!c->redundant)
		{
#if !defined(NSUBSUMPTION) && (!defined(NREDUCE) || !defined(NELIMINATION))
		  if (keep)
		    mark_subsume_variable (solver, INDEX (lit));
#endif
#ifndef NELIMINATION
		  if (!keep)
		    mark_eliminate_literal (solver, lit);
#endif
		}
	      if (keep)
		lits[new_size++] = lit;
              else {
#ifdef NWATCHES
                    disconnect_literal (solver, lit, c);
#endif
              }
	    }
	  assert (new_size < old_size);
	  assert (new_size == size);
	  if (!c->shrunken)
	    {
	      c->shrunken = true;
	      lits[old_size - 1] = INVALID;
	    }
	  c->size = new_size;
	  trace_and_check_clause_addition (solver, c, INVALID);
	  trace_and_check_deletion (solver, SIZE_STACK (solver->clause),
				    solver->clause.begin);
	  CLEAR_STACK (solver->clause);
	  if (!c->redundant
#ifndef NGLUE
	      && c->glue >= new_size
#endif
	    )
	    {
	      promote_clause (solver, c, new_size - 1);
	    }
#ifndef NWATCHES
	  unwatch_literal (solver, litA, c);
	  unwatch_literal (solver, litB, c);
#endif

#ifndef NVIRTUAL
	  if (new_size == 2)
	    {
	      assert (EMPTY_STACK (solver->clause));
	      PUSH (solver->clause, c->literals[0]);
	      PUSH (solver->clause, c->literals[1]);
	      add_new_binary_and_watch_it (solver, c->redundant);
	      CLEAR_STACK (solver->clause);
	      vivify_mark_garbage (solver, c,
				   "vivify shortened to binary clause");
	    }
	  else
#endif
	    {
#ifndef NCACHE
	      c->search = 0;
#endif
	      LOGCLS (c, "vivified shrunken");
	      INC (vivify_strengthened);

#ifndef NWATCHES
	      // Beware of 'stale blocking literals' ... so rewatch if shrunken.
	      watch_clause (solver, c);
#else
              count_clause (solver, c);
#endif
	    }
	  res = true;
	}
      else if (irredundant && !c->redundant)
	{
	  INC (vivify_subsume);
	  vivify_mark_garbage (solver, c, "vivify subsumed (learn)");
	  res = true;
	}
      else
	{
	  LOG ("vivify failed");
	  res = false;
	}
    }

  return res;
}

static bool
vivify_analyze (struct satch *solver, struct clause *c,
		struct clause *conflict, bool *irredundant_ptr)
{
  assert (conflict);
  assert (!EMPTY_STACK (solver->analyzed));
  LOGCLS (conflict, "vivify analyze: marking");

  signed char *vivify_marks = solver->vivify_marks;
  signed char *marks = solver->marks;
  for (all_literals_in_clause (lit, c))
    {
      LOG ("marking literal %s %s", LOGLIT (lit), LOGLIT (NOT (lit)));
      vivify_mark_literal (solver, lit);
    }

  bool subsumed = false;

  if (c->redundant || !conflict->redundant)
    {
      subsumed = true;
      for (all_literals_in_clause (lit, conflict))
	{
	  const signed char value = satch_fixed (solver, lit);
	  if (value < 0)
	    continue;
	  assert (!value);
	  if (vivify_marked_literal (solver, lit) > 0)
	    continue;
	  subsumed = false;
	  break;
	}
      if (subsumed)
	LOGCLS (conflict, "vivify subsuming");
    }

  size_t analyzed = 0;
  bool irredundant = conflict && !conflict->redundant;

  const unsigned *const levels = solver->levels;
  const signed char *const values = solver->values;
  struct clause *const *const reasons = solver->reasons;

  while (analyzed < SIZE_STACK (solver->analyzed))
    {
      const unsigned idx = ACCESS (solver->analyzed, analyzed).idx;
      const unsigned lit = values[LITERAL (idx)] > 0 ?
	LITERAL (idx) : NOT (LITERAL (idx));
      assert (values[lit]);
      const unsigned not_lit = NOT (lit);
      struct clause *const reason = reasons[INDEX (lit)];
      analyzed++;
      assert (levels[idx]);
      assert (marks[idx] & ANALYZED);
      if (!reasons[idx])
	{
	  LOG ("vivify analyzing decision %s", LOGLIT (not_lit));
	  PUSH (solver->clause, not_lit);
	}
#ifndef NBLOCK
      else if (is_tagged_clause (reason))
	{
	  const unsigned other = tagged_clause_to_literal (reason);
	  const bool redundant = tagged_clause_to_redundant (reason);
	  if (redundant)
	    irredundant = false;
	  assert (values[other] < 0);
	  assert (levels[INDEX (other)]);
	  if (c->redundant || !redundant)
	    {
	      if (vivify_marked_literal (solver, lit) < 0 &&
		  vivify_marked_literal (solver, other) < 0)
		{
		  LOG ("vivify subsuming by binary clause %s %s",
		       LOGLIT (lit), LOGLIT (other));
		  subsumed = true;
		}
	    }
	  if (marks[INDEX (other)] & ANALYZED)
	    continue;
	  LOG ("vivify analyzing %s reason %s %s",
	       LOGLIT (lit), LOGLIT (lit), LOGLIT (other));
	  mark_analyzed (solver, INDEX (other));
	}
#endif
      else
	{
	  LOGCLS (reason, "vivify analyzing %s reason", LOGLIT (lit));
	  if (reason->redundant)
	    irredundant = false;
	  bool subsuming = vivify_marked_literal (solver, lit);
	  for (all_literals_in_clause (other, reason))
	    {
	      if (other == lit)
		continue;
	      if (other == not_lit)
		continue;
	      assert (values[other] < 0);
	      if (!levels[INDEX (other)])
		continue;
	      if (!vivify_marked_literal (solver, other))
		subsuming = false;
	      if (marks[INDEX (other)] & ANALYZED)
		continue;
	      mark_analyzed (solver, INDEX (other));
	    }
	  if (subsuming && (c->redundant || !reason->redundant))
	    {
	      subsumed = true;
	      LOGCLS (reason, "vivify subsuming");
	    }
	}
    }

  for (all_literals_in_clause (lit, c))
    {
      LOG ("unmarking literal %s %s", LOGLIT (lit), LOGLIT (NOT (lit)));
      unmark_literal (vivify_marks, lit);
    }

  const size_t size = SIZE_STACK (solver->clause);
  assert (size > 0);
  if (subsumed)
    {
      if (size == 1)
	{
	  LOG ("ignoring subsumed and instead learning unit clause");
#ifndef NDEBUG
	  assert (solver->level);
	  const unsigned decision =
	    *ACCESS (solver->control, solver->level - 1).trail;
	  const unsigned unit = ACCESS (solver->clause, 0);
	  assert (NOT (unit) == decision);
#endif
	  subsumed = false;
	}
      else
	LOGTMP ("vivify ignored learned");
    }
  if (!subsumed)
    {
      *irredundant_ptr = irredundant;
      LOGTMP ("vivify learned");
    }

  return subsumed;
}

static void
vivify_reset_analyzed (struct satch *solver)
{
  signed char *marks = solver->marks;
  for (all_elements_on_stack (struct analyzed, analyzed, solver->analyzed))
    {
      const unsigned idx = analyzed.idx;
      marks[idx] &= ~ANALYZED;
    }
  CLEAR_STACK (solver->analyzed);
  CLEAR_STACK (solver->clause);
}

#ifndef NVIVIFYIMPLY
static struct clause *
vivify_unit_conflict (struct satch *solver, unsigned lit)
{
  assert (solver->values[lit] > 0);
  const unsigned idx = INDEX (lit);
  LOG ("vivify analyzing conflict unit %s", LOGLIT (NOT (lit)));
  assert (!(solver->marks[idx] & ANALYZED));
  struct clause *conflict;
  struct clause *const reason = solver->reasons[idx];

#ifndef NBLOCK
  if (is_tagged_clause (reason))
    {
      conflict = untag_clause (solver, 0, lit, reason);
    }
  else
#endif
    conflict = reason;
  mark_analyzed (solver, idx);
  PUSH (solver->clause, lit);
  return conflict;
}
#endif


static bool
vivify_clause (struct satch *solver, struct clause *c, unsigned *counts)
{
  assert (!c->garbage);
  assert (!solver->inconsistent);
  const unsigned *levels = solver->levels;
  struct unsigned_stack *sorted = &solver->sorted;

  LOGCLS (c, "trying to vivify candidate");
  CLEAR_STACK (*sorted);

  for (all_literals_in_clause (lit, c))
    {
      const signed char value = satch_fixed (solver, lit);
      if (value < 0)
	continue;
      if (value > 0)
	{
	  vivify_mark_garbage (solver, c, "root-level satisfied");
	  break;
	}
      PUSH (*sorted, lit);
    }


  if (c->garbage)
    return false;
  const unsigned non_false = SIZE_STACK (*sorted);

  assert (1 < non_false);
  assert (non_false <= c->size);

#ifndef NLOGGING
  if (!non_false)
    LOG ("no root level falsified literal");
  else if (non_false == c->size)
    LOG ("all literals root level unassigned");
  else
    LOG ("found %u root level non-falsified literals", non_false);
#endif
  if (non_false == 2)
    {
      LOGCLS (c, "skipping actually binary");
      return false;
    }

  unsigned unit = INVALID;

  for (all_literals_in_clause (lit, c))
    {
      const signed char value = solver->values[lit];
      if (value < 0)
	continue;
      if (!value)
	{
	  unit = INVALID;
	  break;
	}
      assert (value > 0);
      if (unit != INVALID)
	{
	  unit = INVALID;
	  break;
	}
      unit = lit;
    }
  if (unit == INVALID)
    LOG ("non-reason candidate clause");
  else
    {
      LOG ("candidate is the reason of %s", LOGLIT (unit));
      const unsigned level = levels[INDEX (unit)];
      assert (level > 0);
      LOG ("forced to backtrack to level %u", level - 1);
      backtrack (solver, level - 1);
    }

  vivify_sort_stack_by_counts (solver, counts, sorted);

  unsigned implied = INVALID;
  unsigned falsified = 0;
  unsigned satisfied = 0;
  struct clause *conflict = 0;
  unsigned level = 0;
  bool res = false;
  assert (non_false == SIZE_STACK (*sorted));
  for (all_elements_on_stack (unsigned, lit, *sorted))
    {
      if (level++ < solver->level)
	{
	  struct level frame = ACCESS (solver->control, level - 1);
	  const unsigned not_lit = NOT (lit);
	  if (*frame.trail == not_lit)
	    {
	      LOG ("reusing assumption %s", LOGLIT (not_lit));
	      INC (vivify_reused);
	      INC (vivify_probes);
	      assert (solver->values[lit] < 0);
	      continue;
	    }

	  LOG ("forced to backtrack to decision level %u", level - 1);
	  backtrack (solver, level - 1);
	}
      const signed char value = solver->values[lit];
      assert (!value || levels[INDEX (lit)] <= level);
      if (!value)
	{
	  LOG ("literal %s unassigned", LOGLIT (lit));
	  const unsigned not_lit = NOT (lit);
	  INC (vivify_probes);
	  solver->level++;
	  assign (solver, not_lit, 0, false);
	  assert (solver->level >= 1);
	  conflict = vivify_boolean_constraint_propagation (solver, c);
	  if (!conflict)
	    continue;
	  vivify_binary_or_large_conflict (solver, conflict);
	  assert (!EMPTY_STACK (solver->analyzed));
	  break;
	}

      if (value < 0)
	{
	  assert (levels[INDEX (lit)]);
	  LOG ("literal %s already falsified", LOGLIT (lit));
	  falsified++;
	  continue;
	}

      satisfied++;
      assert (value > 0);
      assert (levels[INDEX (lit)]);
      LOG ("literal %s already satisfied", LOGLIT (lit));

#ifndef NVIVIFYIMPLY
      if (!c->redundant)
	{
	  implied = lit;
	  conflict = vivify_unit_conflict (solver, lit);
	  assert (!EMPTY_STACK (solver->analyzed));
	  assert (conflict);
	}
      else
	{
	  vivify_mark_garbage (solver, c, "vivify implied");
	  INC (vivify_implied);
	  res = true;
	}
#endif
      break;
    }

  if (c->garbage)
    {
      assert (!conflict);
      assert (EMPTY_STACK (solver->analyzed));
    }
  else if (conflict)
    {
      assert (!EMPTY_STACK (solver->analyzed));
      assert (solver->level);
      bool irredundant;
      const bool subsumed =
	vivify_analyze (solver, c, conflict, &irredundant);

      backtrack (solver, solver->level - 1);

      if (subsumed)
	{
	  vivify_mark_garbage (solver, c, "vivify subsumed");
	  LOGCLS (c, "subsuming clause: ");
	  INC (vivify_subsume);
	  INC (subsumed);
	  res = true;
	}
      else
	res = vivify_learn (solver, c, non_false, irredundant, implied);
      vivify_reset_analyzed (solver);
    }
  else if (falsified && !satisfied)
    {
      LOG ("vivified %u false literals", falsified);
      assert (EMPTY_STACK (solver->clause));
      struct clause *const *const reasons = solver->reasons;
      assert (non_false == SIZE_STACK (*sorted));
      for (all_elements_on_stack (unsigned, lit, *sorted))
	{
	  const unsigned idx = INDEX (lit);
	  assert (levels[idx]);
	  if (reasons[idx])
	    continue;
	  assert (!(solver->marks[idx] & ANALYZED));
	  mark_analyzed (solver, idx);
	  PUSH (solver->clause, lit);
	}
      res = vivify_learn (solver, c, non_false, false, INVALID);
      vivify_reset_analyzed (solver);
    }
  else
    {
      assert (EMPTY_STACK (solver->analyzed));
      LOG ("vivify failed");
    }

  if (!res)
    return false;

  INC (vivified);

  assert (EMPTY_STACK (solver->analyzed));
  assert (EMPTY_STACK (solver->clause));
  return true;
}

static bool
simplify_vivification_candidate (struct satch *solver, struct clause *const c)
{
  assert (!solver->level);
  assert (!c->garbage);
  bool satisfied = false;
  assert (EMPTY_STACK (solver->clause));
  const signed char *const values = solver->values;
  LOGCLS (c, "simplifying for vivification");
  for (all_literals_in_clause (lit, c))
    {
      const signed char value = values[lit];
      if (value > 0)
	{
	  satisfied = true;
	  mark_garbage (solver, c, "vivification satisfied candidate");
	  break;
	}
      if (!value)
	PUSH (solver->clause, lit);
    }
  unsigned non_false = SIZE_STACK (solver->clause);
  if (satisfied)
    {
      CLEAR_STACK (solver->clause);
      return true;
    }
  if (non_false == c->size)
    {
      CLEAR_STACK (solver->clause);
      return false;
    }
  assert (1 < non_false);
  assert (non_false <= c->size);

#ifdef NWATCHES
      for (all_literals_in_clause (lit, c)) {
        disconnect_literal (solver, lit, c);
      }
#endif

#ifndef NVIRTUAL
  if (non_false == 2)
    {
#ifdef LOGGING
      const unsigned first = ACCESS (solver->clause, 0);
      const unsigned second = ACCESS (solver->clause, 1);
#endif
      trace_and_check_temporary_addition (solver);
      LOGBIN (c->redundant, first, second, "vivification shrunken candidate");
      add_new_binary_and_watch_it (solver, c->redundant);
      mark_garbage (solver, c, "vivification shrunken candidate");
    }
  else
#endif
    {
      const unsigned old_size = c->size;
      unsigned new_size = 0, *lits = c->literals;
      CLEAR_STACK (solver->clause);
      for (unsigned i = 0; i < old_size; i++)
	{
	  const unsigned lit = lits[i];
	  PUSH (solver->clause, lit);
	  const signed char value = solver->values[lit];
	  if (value != 0 && solver->levels[INDEX (lit)] == 0)
	    continue;
	  assert (value <= 0);
	  if (value < 0)
	    continue;
	  lits[new_size++] = lit;
	}
#ifndef NVIRTUAL
      assert (2 < new_size);
#endif
      assert (new_size == non_false);
      assert (new_size < old_size);
      c->size = new_size;
#ifndef NCACHE
      c->search = 0;
#endif
      if (c->redundant
#ifndef NGLUE
	  && c->glue >= new_size
#endif
	)
	promote_clause (solver, c, new_size - 1);
      if (!c->shrunken)
	{
	  c->shrunken = true;
	  lits[old_size - 1] = INVALID;
	}
      LOGCLS (c, "vivification shrunken candidate");
      trace_and_check_clause_addition (solver, c, INVALID);
      trace_and_check_deletion (solver, SIZE_STACK (solver->clause),
				solver->clause.begin);
#ifdef NWATCHES
      connect_clause (solver, c);
      count_clause (solver, c);
#endif

    }
  CLEAR_STACK (solver->clause);
  return false;
}

static void
schedule_vivification_candidates (struct satch *solver, unsigned *counts
#ifdef LOGGING
				  , const char *type
#endif
				  , bool redundant
#ifndef NTIER2
				  , bool tier2
#endif
  )
{
  unsigned lower_glue_limit, upper_glue_limit;
#ifndef NTIER2
  if (tier2)
    {
      lower_glue_limit = tier1_glue_limit + 1;
      upper_glue_limit = tier2_glue_limit;
    }
  else
#endif
#ifndef NTIER1
    {
      lower_glue_limit = 0;
      upper_glue_limit = tier1_glue_limit;
    }
#endif
#if (defined(NTIER1) && defined(NTIER2)) || defined(NGLUE)
    {
      lower_glue_limit = 0;
      upper_glue_limit = 10;
    }

#endif
  size_t prioritized = 0;
  for (unsigned prioritize = 0; prioritize < 2; prioritize++)
    {
      if (!redundant)
	{
	  for (all_irredundant_clauses (c))
	    {
	      if (c->garbage)
		continue;
	      if (c->redundant)
		continue;
#ifdef NVIRTUAL
	      if (c->size == 2)
		continue;
#endif
	      if (c->vivify != prioritize)
		{
		  continue;
		}
	      if (simplify_vivification_candidate (solver, c))
		continue;
	      if (prioritize)
		prioritized++;
	      vivify_count_clause (c, counts);
	      PUSH (solver->vivification_schedule, c);
	    }
	}
      else
	{
	  for (all_redundant_clauses (c))
	    {
	      if (c->garbage)
		continue;
	      if (!c->redundant)
		continue;
#ifdef NVIRTUAL
	      if (c->size == 2)
		continue;
#endif

#if !(defined(NTIER1) && defined(NTIER2)) && !defined(NGLUE)
	      if (c->glue < lower_glue_limit)
		continue;
	      if (c->glue > upper_glue_limit)
		continue;
#else
	      if (c->size < lower_glue_limit)
		continue;
	      if (c->size > upper_glue_limit)
		continue;
#endif
	      if (c->vivify != prioritize)
		{
		  continue;
		}
	      if (simplify_vivification_candidate (solver, c))
		continue;
	      if (prioritize)
		prioritized++;
	      vivify_count_clause (c, counts);
	      PUSH (solver->vivification_schedule, c);
	    }
	}
    }

#ifdef LOGGING
  size_t scheduled = SIZE_STACK (solver->vivification_schedule);
#endif
  if (prioritized)
    {
      LOG ("prioritized %zu %s clauses %.0f%%", prioritized,
	   type, percent (prioritized, scheduled));
    }
  else
    {
      LOG ("prioritized all %zu clauses %s", scheduled, type);
      for (all_pointers_on_stack
	   (struct clause, c, solver->vivification_schedule))
	{
#ifndef NVIRTUAL
	  assert (!is_tagged_clause (c));
#endif
	  c->vivify = true;
	}
    }
}

enum round
{
#if (defined(NTIER1) && defined(NTIER1)) || defined(NGLUE)
  REDUNDANT_ROUND = 0,
#endif
#ifndef NTIER1
  REDUNDANT_TIER1_ROUND = 1,
#endif
#ifndef NTIER2
  REDUNDANT_TIER2_ROUND = 2,
#endif
  IRREDUNDANT_ROUND = 3
};

static size_t
vivify_round (struct satch *solver, unsigned round, uint64_t delta,
	      double effort)
{
  assert (EMPTY_STACK (solver->vivification_schedule));
  char tag;
#ifdef LOGGING
  const char *type;
#if (defined (NTIER1) && defined (NTIER2)) || defined(NGLUE)
  if (round == REDUNDANT_ROUND)
    {
      type = "redundant";
      tag = 'u';
    }
  else
#endif
#ifndef NTIER2
  if (round == REDUNDANT_TIER2_ROUND)
    {
      type = "redundant";
      tag = 'u';
    }
  else
#endif
#ifndef NTIER1
  if (round == REDUNDANT_TIER1_ROUND)
    {
      type = "redundant";
      tag = 'v';
    }
  else
#endif
    {
      assert (round == IRREDUNDANT_ROUND);
      type = "irredundant";
      tag = 'w';
    }
#else
#if (defined (NTIER1) && defined (NTIER2)) || defined(NGLUE)
  if (round == REDUNDANT_ROUND)
    {
      tag = 'u';
    }
  else
#endif
#ifndef NTIER2
  if (round == REDUNDANT_TIER2_ROUND)
    {
      tag = 'u';
    }
  else
#endif
#ifndef NTIER1
  if (round == REDUNDANT_TIER1_ROUND)
    {
      tag = 'v';
    }
  else
#endif
    {
      assert (round == IRREDUNDANT_ROUND);
      tag = 'w';
    }
#endif

  flush_large_watches (solver);
#ifndef NVIVIFICATIONLIMITS
  const uint64_t scaled = effort * delta;
  uint64_t start = solver->statistics.probing_ticks;
  const uint64_t ticks_limit = start + scaled;
#else
  (void) effort;
  (void) delta;
  const uint64_t ticks_limit = UINT64_MAX;
#endif
  bool redundant, tier2;
#if defined(NGLUE)
  if (round == REDUNDANT_ROUND)
    {
      redundant = true;
    }
  else
#endif
#if (defined (NTIER1) && defined (NTIER2)) || defined(NGLUE)
  if (round == REDUNDANT_ROUND)
    {
       redundant = true;
    }
  else
#endif
#ifndef NTIER1
  if (round == REDUNDANT_TIER1_ROUND)
    redundant = true, tier2 = false;
  else
#endif
#ifndef NTIER2
  if (round == REDUNDANT_TIER2_ROUND)
    redundant = tier2 = true;
  else
#endif
    {
      assert (round == IRREDUNDANT_ROUND);
      redundant = tier2 = false;
    }

  unsigned *counts = calloc (LITERALS, sizeof (unsigned));

  if (!counts)
    fatal_error ("could not allocate counts for vivification");
  struct clauses *schedule = &solver->vivification_schedule;


  schedule_vivification_candidates (solver, counts,
#ifdef LOGGING
				    type,
#endif
				    redundant
#ifndef NTIER2
				    , tier2
#endif
    );
  const size_t scheduled = SIZE_STACK (*schedule);
#ifdef LOGGING
  const size_t total =
    (round ==
     IRREDUNDANT_ROUND) ? solver->statistics.irredundant : solver->statistics.
    redundant;
#endif

  LOG ("scheduled %zu %s clauses %.0f%% of %zu", scheduled, type,
       percent (scheduled, total), total);
  size_t vivified = 0, tried = 0;

  sort_vivification_candidates (solver, schedule, counts);
  watch_large_clauses (solver);

  while (!EMPTY_STACK (*schedule))
    {
      if (solver->statistics.probing_ticks > ticks_limit)
	break;
      struct clause *c = POP (*schedule);
      if (c->garbage)
	continue;
      tried++;
      if (vivify_clause (solver, c, counts))
	++vivified;
      c->vivify = false;
      if (solver->inconsistent)
	break;
    }

  if (solver->level)
    backtrack (solver, 0);
  if (!solver->inconsistent)
    {
      size_t remain = SIZE_STACK (*schedule);
      const bool keep = true;
      size_t prioritized = 0;
      if (remain)
	{
	  while (!EMPTY_STACK (*schedule))
	    {
	      struct clause *c = POP (*schedule);
	      if (!c->vivify)
		continue;
	      prioritized++;
	      if (!keep)
		c->vivify = false;
	    }
	  if (!prioritized)
	    LOG ("no prioritized %s clauses left", type);
	  else if (keep)
	    LOG ("keeping %zu %s clauses prioritized %.0f%%",
		 prioritized, type, percent (prioritized, remain));
	}
      else
	LOG ("all scheduled %s clauses tried", type);
    }

  CLEAR_STACK (*schedule);
  assert (EMPTY_STACK (solver->clause));

  report (solver, 1, tag);
  free (counts);
  return scheduled;
}

#if (defined(NTIER1) && defined(NTIER1)) || defined(NGLUE)
static size_t
vivify_redundant (struct satch *solver, uint64_t delta, double effort)
{
  return vivify_round (solver, REDUNDANT_ROUND, delta, effort);
}
#endif
#ifndef NTIER1
static size_t
vivify_redundant_tier1 (struct satch *solver, uint64_t delta, double effort)
{
  return vivify_round (solver, REDUNDANT_TIER1_ROUND, delta, effort);
}
#endif

#ifndef NTIER2
static size_t
vivify_redundant_tier2 (struct satch *solver, uint64_t delta, double effort)
{
  return vivify_round (solver, REDUNDANT_TIER2_ROUND, delta, effort);
}
#endif

static void
vivify_irredundant (struct satch *solver, uint64_t redundant_scheduled,
		    uint64_t delta, double effort)
{

  const double factor = 10;
  const uint64_t limit = factor * redundant_scheduled;
  uint64_t irredundant_candidates = 0;

  for (all_irredundant_clauses (c))
    {
      assert (!c->redundant);
      if (c->garbage)
	continue;
      else if (++irredundant_candidates > limit)
	break;
    }

  if (irredundant_candidates > limit)
    LOG ("skipping %" PRIu64 " vivify-irredundant "
	 "candidates > limit %" PRIu64 " = %g * %" PRIu64
	 " scheduled redundant clauses",
	 irredundant_candidates, limit, factor, redundant_scheduled);
  else
    {
      LOG ("vivify-irredundant with "
	   "%" PRIu64 " candidates <= %" PRIu64
	   " = %g * %" PRIu64 " scheduled redundant clauses",
	   irredundant_candidates, limit, factor, redundant_scheduled);
      if (irredundant_candidates > redundant_scheduled)
	{
	  LOG ("not sorting %" PRIu64
	       " vivify-irredundant candidates > %" PRIu64
	       " scheduled redundant clauses",
	       irredundant_candidates, redundant_scheduled);
	}

      (void) vivify_round (solver, IRREDUNDANT_ROUND, delta, effort);
    }
}

static uint64_t
vivify_adjustment (struct satch *solver)
{
  return nlogn (1 + solver->statistics.irredundant +
		solver->statistics.redundant);
}

static bool
really_vivify (struct satch *solver)
{
  const uint64_t limit = vivify_adjustment (solver);
  const uint64_t search_ticks = solver->statistics.ticks;
  return limit < search_ticks;
}



#define MINEFFORT 1e4


#define VIVIFYTIER1 3
#define VIVIFYTIER2 6
#define VIVIFYIRREDUNDANT 1
#define VIVIFYEFFORT 100*1e-3

static int
vivify (struct satch *solver)
{
  if (solver->inconsistent)
    return 20;

  if (solver->level)
    update_phases_and_backtrack_to_root_level (solver);
  assert (!solver->level);
  assert (!solver->dense);

  const uint64_t vivifications = INC (vivifications);

#ifndef NLIMITS
  // Update vivification limit for next time
  const uint64_t interval =
    scale_interval (vivification_interval, nlogn, vivifications);
  struct limits *const limits = &solver->limits;
  limits->vivify.conflicts = CONFLICTS + interval;
#endif

  if (!solver->statistics.redundant)
    return 0;
  if (!really_vivify (solver))
    return 0;

  START (vivify);

  solver->vivifying = true;

#ifndef NVIVIFICATIONLIMITS
  const struct statistics *const statistics = &solver->statistics;
  const uint64_t last = statistics->ticks - limits->vivify.search;
  const uint64_t ticks = last < MINEFFORT ? MINEFFORT : last;
  const uint64_t adjustment = vivify_adjustment (solver);
  const uint64_t delta = ticks * VIVIFYEFFORT + adjustment;
#else
  const uint64_t delta = UINT64_MAX;
#endif

  message (solver, 2, "vivification", vivifications,
	   "elimination limit of %" PRIu64 " ticks = %g * search ticks %"
	   PRIu64, TICKS + delta, (double) VIVIFYEFFORT, delta);
  uint64_t redundant_scheduled = 0;
  double sum = VIVIFYTIER1 + VIVIFYTIER2 + VIVIFYIRREDUNDANT;

#ifndef NVIVIFICATIONLIMITS
  const uint64_t vivified = solver->statistics.vivified;
#endif
#if (defined(NTIER1) && defined(NTIER1)) || defined(NGLUE)
  redundant_scheduled += vivify_redundant (solver, delta, VIVIFYTIER2 / sum);
#endif
#ifndef NTIER2
  redundant_scheduled +=
    vivify_redundant_tier2 (solver, delta, VIVIFYTIER2 / sum);
#endif


  if (!solver->inconsistent)
    {
#ifndef NTIER1
      redundant_scheduled +=
	vivify_redundant_tier1 (solver, delta, VIVIFYTIER1 / sum);
#endif

      if (!solver->inconsistent)
	vivify_irredundant (solver, redundant_scheduled, delta,
			    VIVIFYIRREDUNDANT / sum);

    }
  // Finally update limits.

  {

#ifndef NVIVIFICATIONLIMITS
    const uint64_t limit = limits->vivify.conflicts;
    limits->vivify.search = TICKS;
    message (solver, 2, "vivification", vivifications,
	     "%" PRIu64 " vivified, next limit at %" PRIu64 " after %" PRIu64
	     " conflicts", solver->statistics.vivified - vivified, limit,
	     interval);
#endif
  }
  assert (solver->vivifying);
  solver->vivifying = false;
  CLEAR_STACK (solver->vivification_schedule);
  STOP (vivify);

  if (solver->inconsistent)
    return 20;
  else
    return 0;
}

static bool
vivifying (struct satch *solver)
{
#ifdef NCDCL
  if (solver->level)
    return false;
#endif
#ifndef NINPROCESSING
  return solver->limits.vivify.conflicts < CONFLICTS;
#else
  return !solver->statistics.vivifications;
#endif
}

#endif // of '#ifndef NVIVIFICATION'


#ifndef NLIMITS

static void
init_limits (struct satch *solver)
{
  // First initialize all limits.

#ifndef NELIMINATION
#ifndef NINPROCESSING
  solver->limits.eliminate.conflicts = elimination_interval;
#endif
#endif
#ifndef NREDUCE
  solver->limits.reduce.conflicts = reduce_interval;
#endif
#ifndef NREPHASE
  solver->limits.rephase = rephase_interval;
#endif
#ifndef NRESTART
  solver->limits.restart = restart_interval;
#endif
#ifndef NSWITCH
  solver->limits.mode.conflicts = initial_focused_mode_conflicts;
  solver->limits.mode.ticks.limit = initial_focused_mode_ticks;
#endif

#ifndef NVIVIFICATION
  solver->limits.vivify.conflicts = vivification_interval;
#endif
  // Some sanity checking.

#ifdef NSTABLE
  assert (!solver->stable);
#endif
#ifdef NFOCUSED
  assert (solver->stable);
#endif

  (void) solver;
}

#endif
