/*------------------------------------------------------------------------*/

// Update target and best-phases from a consistent trail.  The user has to
// make sure that the trail is consistent though.  For instance in conflict
// analysis we first have to backtrack one level.

#ifndef NTARGET

static void
save_phases (struct satch *solver, signed char *phases)
{
  const signed char *end = solver->values + LITERALS;
  signed char *q = phases, tmp;
  for (const signed char *p = solver->values; p != end; p += 2, q++)
    if ((tmp = *p))
      *q = tmp;
  assert (q == phases + VARIABLES);
}

static void
update_target_phases (struct satch *solver, const unsigned assigned)
{
  const uint64_t targets = INC (targets);
  save_phases (solver, solver->targets);
  solver->target = assigned;
  message (solver, 3, "target", targets, "targeting %u assigned variables "
	   "%.0f%% after %" PRIu64 " conflicts", assigned,
	   percent (assigned, VARIABLES), CONFLICTS);
}

#ifndef NBEST

static void
update_best_phases (struct satch *solver, const unsigned assigned)
{
  const uint64_t bests = INC (bests);
  save_phases (solver, solver->bests);
  solver->best = assigned;
  message (solver, 3, "best", bests, "best trail %u assigned variables "
	   "%.0f%% after %" PRIu64 " conflicts", assigned,
	   percent (assigned, VARIABLES), CONFLICTS);
}

#endif

// Make sure to care for root-level assigned variables when computing the
// number of assigned variables.  Those are flushed from the trail after
// unit propagation on the root-level completes. The trail size itself is
// not correct and makes target and stable phases actually behave badly.

static inline unsigned
assigned_variables (struct satch *solver)
{
  assert (VARIABLES >= solver->unassigned);
  return VARIABLES - solver->unassigned;
}

static void
update_phases (struct satch *solver)
{
  assert (solver->stable);
  const unsigned assigned = assigned_variables (solver);
  if (assigned > solver->target)
    update_target_phases (solver, assigned);
#ifndef NBEST
  if (assigned > solver->best)
    update_best_phases (solver, assigned);
#endif
}

#endif

/*------------------------------------------------------------------------*/

// Backtracking to a certain decision level in essence just unassigns the
// literals assigned on higher decisn level. Then it reset the decision
// level and the propagation pointer.

// This procedure is slightly more complicated though since we first need to
// put back unassigned variables back to the binary heap for (E)VSIDS and
// second update the search index for the VMTF queue. Third without clause
// learning ('NLEARN' defined) learned clauses are only used for computing
// scores and back-jumping and during backtracking have to be deleted.

// Unfortunately this leads to rather complex code due to conditional
// compilation and allowing all combinations of features, including various
// ways to use EVSIDS scores and VMTF queue in stable and focused mode,
// disabling learning and blocking literals.

static void
backtrack (struct satch *solver, unsigned new_level)
{
  LOG ("backtracking to level %u", new_level);
  assert (new_level < solver->level);
#if !defined(NDEBUG) || !defined(NCHRONO) || defined(NCONTROL)
  const unsigned *levels = solver->levels;
#endif
  signed char *values = solver->values;

#ifndef NQUEUE
  struct queue *queue = 0;
  const struct link *links = 0;
  unsigned search = INVALID;
  unsigned max_stamp = INVALID;
#ifndef NHEAP
  if (!solver->stable)
#endif
    {
      queue = get_queue (solver);
      links = queue->links;
      search = queue->search;
      max_stamp = search == INVALID ? 0 : links[search].stamp;
    }
#endif

#ifndef NHEAP
  struct heap *scores = 0;
  const unsigned *pos = 0;
#ifndef NQUEUE
  if (solver->stable)
#endif
    {
      scores = get_scores (solver);
      pos = scores->pos;
    }
#endif

#ifdef NLEARN
  struct clause *const *const reasons = solver->reasons;
#endif

#ifdef NWATCHES
  const unsigned * const propagated = solver->trail.propagate;
#endif
  struct trail *trail = &solver->trail;
#ifndef NCONTROL
  unsigned *target_lit = ACCESS (solver->control, new_level).trail;
  assert (target_lit >= solver->trail.begin);
  assert (target_lit < solver->trail.end);
  assert (target_lit <= trail->propagate);
  unsigned *starting = target_lit;

#endif
#if !defined(NCHRONO) && !defined(NLOGGING)
  unsigned *position = solver->position;
  int starting_position = target_lit - solver->trail.begin;
  LOG ("backtracking to position %d corresponding", starting_position);
#endif

#ifndef NCHRONO
  trail->propagate = target_lit;
  int reassigned = 0;
#endif

#ifndef NCONTROL
  while (target_lit != solver->trail.end)
    {
      const unsigned lit = *target_lit;
#ifdef NWATCHES
      const unsigned *p = target_lit;
#endif
      ++target_lit;
      const unsigned idx = INDEX (lit);
      assert (starting <= target_lit);
#if !defined(NCHRONO) || !defined(NDEBUG)
      const unsigned lit_level = levels[idx];
#endif
#else
  const unsigned * const begin = trail->begin;
  unsigned *p = trail->end;
  while (p != begin)
    {
      unsigned * next = p - 1;
      const unsigned lit = *next;
      const unsigned idx = INDEX (lit);
      const unsigned lit_level = levels[idx];
      if (lit_level == new_level)
	break;
      p = next;
#endif
      LOG ("unassign %s", LOGLIT (lit));
      assert (solver->unassigned < solver->size);
#ifndef NCHRONO
      assert (trail->end > starting);
      assert (starting_position == starting - trail->begin);
      if (lit_level <= new_level)
	{
	  LOG ("keeping literal %s", LOGLIT (lit));
	  *starting = lit;
	  position[idx] = starting_position;
	  ++reassigned;
	  ++starting;
	  ++starting_position;
#ifdef NWATCHES
	  if (p < propagated)
	    unpropagate_literal (solver, lit);
#endif
	  continue;
	}
      LOG ("popping literal %s", LOGLIT (lit));
#else
      assert (lit_level > new_level);
#endif
      solver->unassigned++;
      const unsigned not_lit = NOT (lit);

#if !defined(NELIMINATION) && !defined(NLEARN)
      assert (values[lit] > 0);
      assert (values[not_lit] < 0);
#else
      // Both Might be flipped in 'extend_solution'.
      //
      assert (values[lit]);
      assert (values[not_lit]);
#endif
      assert (values[lit] == -values[not_lit]);

      values[lit] = 0;
      values[not_lit] = 0;

#ifdef NLEARN
      struct clause *reason = reasons[idx];
      if (reason &&
#ifdef NCDCL
          reason != DUMMY_REASON &&
#endif
#ifndef NBLOCK
	  !is_tagged_clause (reason) &&
#endif
	  reason->redundant)
	(void) delete_clause (solver, reason);
#endif
#ifndef NQUEUE
      if (links)
	{
	  const unsigned stamp = links[idx].stamp;
	  if (stamp > max_stamp)
	    search = idx, max_stamp = stamp;
	}
#endif
#ifndef NHEAP
      if (pos && pos[idx] == INVALID)
	push_heap (solver, scores, idx);
#endif
#ifdef NWATCHES
      if (p < propagated)
	unpropagate_literal (solver, lit);
      else {
	LOG ("%ld and pos vs propagated %ld", p - propagated, p - trail->propagate);
      }
#endif
    }

#ifndef NCONTROL
  solver->trail.end = starting;
#ifdef NCHRONO
  trail->propagate = trail->end;
#endif
#else
  LOG ("p = %s", LOGLIT (*p));
  trail->end = trail->propagate = p;
#endif
#ifndef NQUEUE
  if (queue)
    {
      LOG ("searched variable index %u", search);
      queue->search = search;
    }
#endif

#ifndef NCONTROL
  solver->control.end = solver->control.begin + new_level;
  assert (new_level == SIZE_STACK (solver->control));
#endif

#ifdef DLIS
  LOG ("backtracking DLIS stack to level %d", new_level);
  solver->irred_sat_upto.end = solver->irred_sat_upto.begin + new_level;
  solver->red_sat_upto.end = solver->red_sat_upto.begin + new_level;
  assert (new_level == SIZE_STACK (solver->irred_sat_upto));
#endif

#ifndef NCHRONO
  assert (trail->propagate <= trail->end);
#endif
  solver->level = new_level;
}

#if !defined(NREDUCE) || !defined(NELIMINATION) || !defined(NVIVIFICATION)

static void
update_phases_and_backtrack_to_root_level (struct satch *solver)
{
  if (!solver->level)
    return;
#ifndef  NTARGET
  if (solver->stable)
    update_phases (solver);
#endif
  backtrack (solver, 0);

#ifndef NCHRONO
  const struct clause *conflict = boolean_constraint_propagation (solver);
  if (conflict)
    solver->inconsistent = true;
#endif
}

#endif