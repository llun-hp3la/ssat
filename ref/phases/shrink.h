/*------------------------------------------------------------------------*/
#ifndef NSORTDEDUCED

// Shrinking requires that the temporary learned clause is partitioned into
// its decision levels.  Each such partition is called a block and we
// require the blocks to be in descending level order.  It is in general
// beneficial to sort literals in descending level order in learned clauses
// too and thus we sort the deduced clause even if shrinking is disabled.

#ifndef NRADIXSORT

#define RANK_LITERAL_BY_INVERSE_LEVEL(LIT)	(~levels[INDEX (LIT)])

static void
sort_deduced_clause (struct satch *solver)
{
  const unsigned *const levels = solver->levels;
  RSORT (unsigned, unsigned, solver->clause, RANK_LITERAL_BY_INVERSE_LEVEL);
}

#else

// Without radix sort we need to get the levels from the sorted array and
// thus have to allocate a temporary array with literals and their levels.

// Since we want stable sorting (to match the radix-sort version) we also
// add a position argument and thus keep literals in their original order
// in the clause within one block (literals with the same level).

struct lit_level_pos
{
  unsigned lit, level, pos;
};

static int
cmp_lit_level_pos (const void *p, const void *q)
{
  struct lit_level_pos *l = (struct lit_level_pos *) p;
  struct lit_level_pos *k = (struct lit_level_pos *) q;
  if (l->level > k->level)
    return -1;
  if (l->level < k->level)
    return 1;
  assert (l->pos != k->pos);
  return l->pos < k->pos ? -1 : 1;
}

static void
sort_deduced_clause (struct satch *solver)
{
  struct unsigned_stack *clause = &solver->clause;
  const unsigned size = SIZE_STACK (*clause);
  const size_t bytes = size * sizeof (struct lit_level_pos);
  struct lit_level_pos *a = malloc (bytes);
  if (!a)
    out_of_memory (bytes);
  const unsigned *levels = solver->levels;
  unsigned pos = 0;
  for (all_elements_on_stack (unsigned, lit, *clause))
    {
      struct lit_level_pos *p = a + pos;
      p->lit = lit;
      p->level = levels[INDEX (lit)];
      p->pos = pos++;
    }
  qsort (a, size, sizeof *a, cmp_lit_level_pos);
  const struct lit_level_pos *const end = a + size;
  unsigned *c = clause->begin;
  for (const struct lit_level_pos * p = a; p != end; p++)
    *c++ = p->lit;
  free (a);
}

#endif

#endif

/*------------------------------------------------------------------------*/

// The 'ANALYZED' flag is used for 'analyze' but also during minimization.

#define ANALYZED 1		// Literal seen during conflict analysis.

// Conflict clause minimization is implemented here.

#ifndef NMINIMIZE

// The following two flags can be set independently of 'ANALYZED' and thus
// have different bits.  During shrinking we additionally have 'SHRUNKEN'.

#define REMOVABLE 2		// Literal can be be minimized.
#define POISONED 4		// Literal can not be minimized.

static void
mark_removable (struct satch *solver, unsigned idx)
{
  assert (!(solver->marks[idx] & REMOVABLE));
  solver->marks[idx] |= REMOVABLE;
  PUSH (solver->removable, idx);
  LOG ("removable %s", LOGVAR (idx));
}

static void
mark_poisoned (struct satch *solver, unsigned idx)
{
  assert (!(solver->marks[idx] & POISONED));
  solver->marks[idx] |= POISONED;
  PUSH (solver->poisoned, idx);
  LOG ("poisoned %s", LOGVAR (idx));
}

// Return either 'REMOVABLE' (literal can be removed) or 'POISONED'.

// This recursive function is guarded against stack-overflow by providing an
// additional 'depth' parameter, which is increase with each recursive call.
// If 'depth' hits the 'minimize_depth' limit the procedure conservatively
// assumes that the literal can not be minimized away.

// Previously computed results are cached in mark flags. Root-level
// assigned literals are ignored.  The function aborts negatively if a
// decision variable is reached which has not been marked as being in the
// clause before (marked 'REMOVABLE') or the decision level of the literal
// is not in the learned clause.

static int
minimize_literal (struct satch *solver, unsigned lit, unsigned depth)
{
  const unsigned idx = INDEX (lit);
  signed char mark = solver->marks[idx];
  assert (mark >= 0);
  if (mark & POISONED)
    return POISONED;		// Previously shown not to be removable.
  if (mark & REMOVABLE)
    return REMOVABLE;		// Previously shown to be removable.
  if (depth && (mark & ANALYZED))
    return REMOVABLE;		// Analyzed thus removable (unless start).
  const unsigned level = solver->levels[idx];
  if (!level)
    return REMOVABLE;		// Root-level units can be removed.
  if (depth > minimize_depth)
    return POISONED;		// Avoids deep recursion (stack overflow).
#ifndef NCONTROL
  if (!depth && ACCESS (solver->control, level - 1).seen.count < 2)
    return POISONED;
  if (solver->position[idx] <=
      ACCESS (solver->control, level - 1).seen.earliest)
    return POISONED;
#endif
  assert (solver->values[lit] < 0);
  struct clause *reason = solver->reasons[idx];
  if (!reason)
    return POISONED;		// Decisions can not be removed.
  if (!solver->frames[level])
    return POISONED;		// Level not pulled into clause.
  int res = REMOVABLE;
#ifndef NBLOCK
  if (is_tagged_clause (reason))
    reason = untag_clause (solver, 0, NOT (lit), reason);
  else
#endif
    INC (ticks);
  const unsigned not_lit = NOT (lit);
  LOGCLS (reason, "trying to minimize %s at depth %u along",
	  LOGLIT (not_lit), depth);
  for (all_literals_in_clause (other, reason))
    {
      if (other == not_lit)
	continue;
      if (minimize_literal (solver, other, depth + 1) == REMOVABLE)
	continue;
      res = POISONED;
      break;
    }
  if (depth)
    {
      if (res == REMOVABLE)
	mark_removable (solver, idx);
      else
	mark_poisoned (solver, idx);
    }
  LOG ("%s %s at depth %u",
       (res == REMOVABLE ? "removable" : "poisoned"), LOGLIT (lit), depth);
  return res;
}

#ifdef NSHRINK

// Minimize the deduced first unique implication point (1st UIP) clause.

// By default ('NSHRINK' undefined) we employ all-UIP shrinking though which
// minimizes (in 'minimize_block') each block of literals in the learned
// clause with the same decision level in the deduced clause separately
// after shrinking unless shrinking was able to replace the whole block by a
// single literal.  Thus with shrinking this function becomes obsolete.

static void
minimize_deduced_clause (struct satch *solver)
{
  assert (EMPTY_STACK (solver->poisoned));
  assert (EMPTY_STACK (solver->removable));

  unsigned *const end = solver->clause.end;
  unsigned *const begin = solver->clause.begin;
  for (unsigned *p = end - 1; p != begin; p--)
    if (minimize_literal (solver, *p, 0) == REMOVABLE)
      *p = INVALID;

  unsigned *q = begin, lit;
  for (const unsigned *p = q; p != end; p++)
    if ((lit = *p) != INVALID)
      *q++ = lit;

  const size_t minimized = end - q;
  solver->clause.end = q;

  LOG ("minimized %zu literals", minimized);
  ADD (minimized, minimized);

  LOGTMP ("minimized");
}

#endif

// Reset the 'POISONED' and 'REMOVABLE' flags set during minimization.

static void
reset_removable_and_poisoned (struct satch *solver)
{
  for (all_elements_on_stack (unsigned, idx, solver->poisoned))
      solver->marks[idx] &= ~POISONED;
  CLEAR_STACK (solver->poisoned);

  for (all_elements_on_stack (unsigned, idx, solver->removable))
      solver->marks[idx] &= ~REMOVABLE;
  CLEAR_STACK (solver->removable);
}

#endif

/*------------------------------------------------------------------------*/

// Mark a literal as 'ANALYZED' if it has not been visited yet during
// conflict analysis (or during reason-side-bumping).  Since the 'analyze'
// function below needs the assignment level of the literal to mark decision
// levels and decide whether the literal is added to the learned clause we
// use that level as return value or 'INVALID' as result if the literal has
// been marked before (or has been assigned on the root-level zero).

static void
mark_analyzed (struct satch *solver, unsigned idx)
{
  assert (!(solver->marks[idx] & ANALYZED));
  solver->marks[idx] |= ANALYZED;
  struct analyzed analyzed;
  analyzed.idx = idx;
#ifndef NSORTANALYZED
  analyzed.stamp = INVALID;
#endif
  PUSH (solver->analyzed, analyzed);
  LOG ("analyzed %s", LOGVAR (idx));
}

static inline unsigned
analyze_literal (struct satch *solver, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  const unsigned lit_level = solver->levels[idx];
  if (!lit_level)
    return INVALID;
  if (solver->marks[idx])
    return INVALID;
  mark_analyzed (solver, idx);
  return lit_level;
}

/*------------------------------------------------------------------------*/

// More thorough shrinking than classical clause minimization by trying to
// find unique implication points on all previous decision levels without
// introducing new decision levels into the learned clause.

#ifndef NSHRINK

// Mark-bit different from 'ANALYZED', 'REMOVABLE', and 'POISONED'.

#define SHRUNKEN 8

static void
mark_shrunken (struct satch *solver, unsigned idx)
{
  assert (!(solver->marks[idx] & SHRUNKEN));
  solver->marks[idx] |= SHRUNKEN;
  PUSH (solver->shrunken, idx);
  LOG ("shrunken %s", LOGVAR (idx));
}

// Reset literals marked 'SHRUNKEN' in any case (successful or unsuccessful).

static void
reset_shrunken (struct satch *solver)
{
  LOG ("resetting %zu shrunken variables", SIZE_STACK (solver->shrunken));
  signed char *marks = solver->marks;
  for (all_elements_on_stack (unsigned, idx, solver->shrunken))
      marks[idx] &= ~SHRUNKEN;
  CLEAR_STACK (solver->shrunken);
}

// Positive case: literals can be shrunken to one unique implication point.

static void
mark_shrunken_as_removable (struct satch *solver)
{
  signed char *marks = solver->marks;
  for (all_elements_on_stack (unsigned, idx, solver->shrunken))
    if (!(marks[idx] & REMOVABLE))
        mark_removable (solver, idx);
}

// Return '0' if literal is removable or has already been shrunken. Return
// '-1' if it can definitely not be shrunken, and '1' if it can in principle
// be shrunken and thus has been marked as such.

// The encoding of these result values has the idea that it matches the
// number of new additionally marked literals by which 'open' is increased
// in 'shrink_block' except that if '-1' is returned the search is aborted.

// On lower decision level than the given level of the considered block we
// use 'minimize_literal' which tries to resolve the literal away based on
// other literals already in the (partially) minimized and shrunken clause.

static int
shrink_literal (struct satch *solver, unsigned block_level, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  const unsigned lit_level = solver->levels[idx];
  if (!lit_level)
    return 0;
  if (solver->marks[idx] & SHRUNKEN)
    return 0;
  if (lit_level < block_level)
    return (minimize_literal (solver, lit, 1) == REMOVABLE) ? 0 : -1;
  mark_shrunken (solver, idx);
  return 1;
}

// In case 'shrink_block' is successful it calls this function and shrinks
// the literals in the clause from 'begin' to 'end' to the given unique
// implication point and further resets the shrunken literals.

static void
shrunken_block (struct satch *solver,
		unsigned *begin, unsigned *end, unsigned uip)
{
  for (unsigned *p = begin; p != end; p++)
    *p = INVALID;
  *begin = NOT (uip);
  const unsigned idx = INDEX (uip);
  if (!(solver->marks[idx] & ANALYZED))
    mark_analyzed (solver, idx);
#ifndef NCONTROL
  const unsigned level = solver->levels[idx];
  if (level != 0)
    {
      struct level *saved = &ACCESS (solver->control, level - 1);
      if (saved->seen.earliest > solver->position[idx])
	saved->seen.earliest = solver->position[idx];
      ++saved->seen.count;
      LOG ("updating level %d with: %d %d", level, saved->seen.earliest,
	   saved->seen.count);
    }
#endif
  mark_shrunken_as_removable (solver);
  reset_shrunken (solver);
}

// Get start of the level-block ending right before 'end' in the temporary
// clause which is assumed to be sorted by decreasing decision levels.

static unsigned *
next_block (struct satch *solver, unsigned *end)
{
  const unsigned *const levels = solver->levels;
  unsigned block_level = INVALID;
  unsigned *begin = end;
  while (solver->clause.begin < begin)
    {
      const unsigned lit = begin[-1];
      const unsigned idx = INDEX (lit);
      const unsigned lit_level = levels[idx];
      if (lit_level > block_level)
	break;
      block_level = lit_level;
      begin--;
    }
  return begin;
}

// Find a first unique implication point of the given block of literals with
// the same decision level in the deduced clause.

static bool
shrink_block (struct satch *solver, unsigned *begin, unsigned *end)
{
  assert (begin < end);
  unsigned open = end - begin;
  if (open < 2)
    return true;		// Already shrunken so avoid 'minimize_block'.

  const unsigned block_level = solver->levels[INDEX (*begin)];
  LOG ("trying to shrink block of size %u at level %u", open, block_level);

  // First mark all literals in the block as 'SHRUNKEN' and also compute
  // the maximum trail position of the literals in this block.

  unsigned trail = 0;
  {
    const unsigned *const position = solver->position;
    assert (EMPTY_STACK (solver->shrunken));
    for (unsigned *p = begin; p != end; p++)
      {
	const unsigned lit = *p;
	const unsigned idx = INDEX (lit);
	mark_shrunken (solver, idx);

	const unsigned pos = position[idx];
	assert (solver->trail.begin[pos] == NOT (lit));
	if (pos > trail)
	  trail = pos;
      }
    assert (SIZE_STACK (solver->shrunken) == open);
  }

  // Now we can start traversing the trail for this block going backward
  // from the last its literal on the trail.  This traversal follows a
  // topological order, i.e., an inverse assignment order, and is similar to
  // the trail traversal in 'analyze' which deduces the learned clause in
  // the first place.  This order allows us to properly maintain 'open', the
  // number of literals marked 'SHRUNKEN' and not yet resolved.  If this
  // number drops to one we have found a unique implication point for this
  // block.  An alternative to this linear traversal along the trail is
  // to use a binary heap (we actually tried a radix heap) or some clever
  // depth first search. The latter however would need to be aborted early
  // if a literal can not be shrunken and probably is more complicated.

  const unsigned *t = solver->trail.begin + trail;
  unsigned uip = INVALID;
  bool failed = false;

  const signed char *const marks = solver->marks;
  struct clause *const *const reasons = solver->reasons;

  while (!failed)
    {
      unsigned idx;
      do
	assert (t >= solver->trail.begin), uip = *t--;
      while (!(marks[idx = INDEX (uip)] & SHRUNKEN));
      if (!--open)
	break;
      struct clause *reason = reasons[idx];
      assert (reason);
#ifndef NBLOCK
      if (is_tagged_clause (reason))
	reason = untag_clause (solver, 0, uip, reason);
      else
#endif
	INC (ticks);
      LOGCLS (reason, "trying to shrink %s along", LOGLIT (uip));
      for (all_literals_in_clause (lit, reason))
	if (lit != uip)
	  {
	    int tmp = shrink_literal (solver, block_level, lit);
	    if ((failed = (tmp < 0)))
	      break;
	    open += (tmp > 0);
	  }
    }

  if (failed)
    reset_shrunken (solver);
  else
    shrunken_block (solver, begin, end, uip);

  LOG ("shrinking of block of size %zu at level %u %s",
       (size_t) (end - begin), block_level, failed ? "failed" : "succeeded");

  return !failed;
}

// Minimize the block if it could not be shrunken.

static void
minimize_block (struct satch *solver, unsigned *begin, unsigned *end)
{
  unsigned minimized = 0;
  for (unsigned *p = begin; p != end; p++)
    if (minimize_literal (solver, *p, 0) == REMOVABLE)
      *p = INVALID, minimized++;
  ADD (minimized, minimized);
  LOG ("minimized %u literals", minimized);
}

// This is the main shrinking function.  It requires the temporary clause to
// be sorted with respect to decreasing decision level of its literals (thus
// 'sort_deduced_clause' has to be called first).

static void
shrink_deduced_clause (struct satch *solver)
{
  assert (EMPTY_STACK (solver->poisoned));
  assert (EMPTY_STACK (solver->removable));

  {
    unsigned *end = solver->clause.end;
    while (end != solver->clause.begin)
      {
	unsigned *begin = next_block (solver, end);
	if (!shrink_block (solver, begin, end))
	  minimize_block (solver, begin, end);
	end = begin;
      }
  }

  // Removed literals of each block are overwritten with 'INVALID' in place
  // and in a last pass we have to flush these invalid literals.

  {
    const unsigned *const end = solver->clause.end;
    unsigned *q = solver->clause.begin, lit;
    for (const unsigned *p = q; p != end; p++)
      if ((lit = *p) != INVALID)
	*q++ = lit;

    const unsigned shrunken = end - q;
    solver->clause.end = q;
    LOG ("shrunken %u literals", shrunken);
    ADD (shrunken, shrunken);
  }

  LOGTMP ("shrunken");
}

#endif

/*------------------------------------------------------------------------*/

// Bumping reason side literals was introduced in the Maple solver in 2016.

// The idea is to also bump those literals in the reason of the literals in
// the learned clauses.  It seems that using target phases during stable
// mode really needs this technique in order to be effective (and the same
// applies to rephasing to best-phases and probably rephasing in general).

#ifndef NBUMPREASONS

static inline void
bump_reason_side_literals (struct satch *solver)
{
  struct averages *a = averages (solver);
  if (unbiased_slow_average (a, a->decision_rate) >=
      bump_reason_decision_rate_limit)
    return;

  struct clause *const *const reasons = solver->reasons;
  for (all_elements_on_stack (unsigned, lit, solver->clause))
    {
      const unsigned idx = INDEX (lit);
      struct clause *reason = reasons[idx];
#ifndef NBLOCK
      if (is_tagged_clause (reason))
	reason = untag_clause (solver, 0, NOT (lit), reason);
#endif
      if (!reason)
	continue;
      for (all_literals_in_clause (other, reason))
	if (analyze_literal (solver, other) != INVALID)
	  INC (reasons);
    }
}

#endif

/*------------------------------------------------------------------------*/

// Sorting the analyzed variable indices to be bumped with respect to their
// enqueue time stamp on the VMTF decision queue makes sure that they keep
// the same relative order on the queue after bumping which empirically
// improves the effectiveness of the decision heuristic (less conflicts).

#ifndef NSORTANALYZED

// The enqueue time stamps could be added to the 'analyzed' stack while
// pushing variable indices to it.  This makes that code more complex given
// all the different ways of disabling and enabling VMTF and sorting.
// Instead we simply put this here to keep that complexity out of 'analyze'.

static void
add_stamps (struct satch *solver)
{
  struct queue *queue = get_queue (solver);
  const struct link *const links = queue->links;
  const struct analyzed *const end = solver->analyzed.end;
  struct analyzed *const begin = solver->analyzed.begin;
  for (struct analyzed * p = begin; p != end; p++)
    p->stamp = links[p->idx].stamp;
}

#ifndef NRADIXSORT

// Ranking function for radix-sorting the analyzed variables stack.

// Without using radix sort the time spent in 'sort_analyzed' can reach 20%
// of the total running time (including both time spent in focused and
// stable mode) even though 'sort_analyzed' is by default only used in
// focused mode for the VMTF decision heuristic.  This might then increase
// relative time spent in focused mode since we do not want to account for
// sorting with our 'ticks' counter.  We have seen cases where this effect
// lead to 70% time spent in focused mode and only 30% time in stable mode.
// Using faster radix sorting allows to achieve a more balanced split of
// search time into focused and stable mode.

// Note that for CaDiCaL and early versions of Kissat we determined
// empirically that quick sort is faster when sorting 800 or less variables.
// With a new optimization which computes upper and lower bounds once for
// all radix rounds, this number of 800 could be reduced to only 32
// elements, where the dedicated inlined quick sort is faster.

// These numbers are with respect to a dedicated fast header only quick sort
// implementation.  For the standard 'qsort' function of the C library which
// requires comparison function call-backs instead of inlined comparison
// this number would be smaller anyhow.  Thus for 'satch' we do not
// implement quick sort at this point.  Note also that quick-sort itself
// usually has some kind of 'leaf-coarsening' and in essence switches to
// insertion sort if for instance the number of elements drops below 10.

#define rank_analyzed(A) (A).stamp

static void
sort_analyzed (struct satch *solver)
{
  add_stamps (solver);
  RSORT (struct analyzed, unsigned, solver->analyzed, rank_analyzed);
}

#else

// Comparison function for 'qsort' to sort variable indices by stamp time.
// Note that, time stamps are unique. Thus we get stable sorting for free.

static int
cmp_analyzed (const void *p, const void *q)
{
  const struct analyzed *a = p, *b = q;
  unsigned s = a->stamp, t = b->stamp;
  return (s < t) ? -1 : 1;
}

static void
sort_analyzed (struct satch *solver)
{
  add_stamps (solver);
  qsort (solver->analyzed.begin, SIZE_STACK (solver->analyzed),
	 sizeof (struct analyzed), cmp_analyzed);
}

#endif
#endif

