/*------------------------------------------------------------------------*/

#ifndef NQUEUE

unsigned
max_stamped_unassigned_variable_on_decision_queue (struct satch *solver)
{
  struct queue *queue = get_queue (solver);
  const struct link *const links = queue->links;
  const signed char *const values = solver->values;

  unsigned idx = queue->search;

  for (;;)
    {
      assert (idx != INVALID);
      const unsigned lit = LITERAL (idx);
      const signed char value = values[lit];
      if (!value)
	break;
      idx = links[idx].prev;
    }
  queue->search = idx;		// Cache search position.

  LOG ("maximum stamped unassigned %s with stamp %u",
       LOGVAR (idx), links[idx].stamp);

  return idx;
}

#endif

#ifndef NHEAP
unsigned
max_score_unassigned_variable_on_binary_heap (struct satch *solver)
{
  const signed char *const values = solver->values;
  struct heap *scores = get_scores (solver);

  unsigned idx;

  for (;;)
    {
      idx = max_heap (scores);
      const unsigned lit = LITERAL (idx);
      const signed char value = values[lit];
      if (!value)
	break;
      pop_heap (solver, scores);
    }

  LOG ("maximum score unassigned %s with score %g",
       LOGVAR (idx), scores->score[idx]);

  return idx;
}

#endif

/*------------------------------------------------------------------------*/

// Decision variable heuristic uses exponential 'VSIDS' in stable mode and
// 'VMTF' in focused mode unless one of these heuristics is disabled.

// The different cases in this function should match those in 'reuse_trail',
// except that the latter is only enabled if bumping is enabled too (thus we
// can replace 'NHEAP' with 'NVSIDS' and 'NQUEUE' with 'NVMTF' there).

#if !defined(DLIS) || !defined(NSAVE)

static unsigned
decide_variable (struct satch *solver)
{
  unsigned idx;

#ifdef DLIS
  idx = max_score_dlis (solver);
#else
#if defined(NHEAP)
  idx = max_stamped_unassigned_variable_on_decision_queue (solver);
#elif defined(NQUEUE)
  idx = max_score_unassigned_variable_on_binary_heap (solver);
#else
  if (solver->stable)
    idx = max_score_unassigned_variable_on_binary_heap (solver);
  else
    idx = max_stamped_unassigned_variable_on_decision_queue (solver);
#endif
#endif
  LOG ("decision %s", LOGVAR (idx));

  return idx;
}

// The decision phase is the value assigned to the decision variable. In the
// default configuration we use 'phase saving', i.e., the previous assigned
// variable to that variable and fall back to the default phase 'true' for
// never assigned variables (unless 'NTRUE' is defined, where the default
// original phase value becomes 'false').  The default value is always
// picked if phase saving is disabled ('NSAVE' is defined).

static int
original_phase (void)
{
#ifndef NTRUE
  return 1;			// Default is 'true'.
#else
  return -1;			// Otherwise 'false' (if 'NTRUE' defined).
#endif
}

static int
decide_phase (struct satch *solver, unsigned idx)
{
  signed char value = 0;
#ifndef NTARGET
  if (solver->stable)
    value = solver->targets[idx];
#endif
#ifndef NSAVE
  if (!value)
    value = solver->saved[idx];
#endif
  if (!value)
    value = original_phase ();
  LOG ("decision phase %d", (int) value);
  (void) idx;			// Prevent unused 'idx' warning.
  return value;
}
#endif

// Pick a decision variable and phase to which it is assigned as decision
// literal. Then increase decision level and assign the decision literal.

static void
decide (struct satch *solver)
{
#ifdef NWATCHES
#ifndef NVIVIFICATION
  if (!solver->vivifying)
#endif
    {
    for (all_irredundant_clauses(clause)) {
      unsigned count = 0;
      if (clause->garbage)
        continue;
      for (all_literals_in_clause(lit, clause)) {
	if (solver->values[lit] != -1)
	  ++count;
      }
      assert (count == clause->count);
    }
    for (all_redundant_clauses(clause)) {
      if (clause->garbage)
        continue;
      unsigned count = 0;
      for (all_literals_in_clause(lit, clause)) {
	if (solver->values[lit] != -1)
	  ++count;
      }
      assert (count == clause->count);
    }
  }
#endif
  START_IF_NCHEAP (decide);
  INC (decisions);

  assert (solver->unassigned);
  assert (!solver->inconsistent);
  assert (solver->level < solver->size);

#ifndef NCHRONO
  assert (solver->level == SIZE_STACK (solver->control));
#endif
  solver->level++;
#if defined(DLIS) && defined(NSAVE)
  const unsigned decision = max_score_dlis (solver);	// actually returns a literal
#else
  const unsigned idx = decide_variable (solver);
  const int value = decide_phase (solver, idx);

  const unsigned lit = LITERAL (idx);
  const unsigned decision = (value < 0 ? NOT (lit) : lit);
  LOG ("decision literal %s", LOGLIT (decision));
#endif
  assign (solver, decision, 0, false);
  STOP_IF_NCHEAP (decide);
}

