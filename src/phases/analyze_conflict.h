/*------------------------------------------------------------------------*/

// The CDCL conflict analysis function.

// Find the highest level present in the conflict. Without chronological backtracking this is
// always the current decision level
#ifndef NCHRONO

static int
find_conflict_level (struct satch *solver, struct clause *conflict,
		     unsigned *forced)
{
  assert (!solver->inconsistent);

  (void) *forced;
  unsigned res = 0;
  int count = 0;
  unsigned *lits = conflict->literals;
  const int size = conflict->size;
  unsigned *const end = lits + size;
  unsigned *const begin = lits;
  for (unsigned *p = begin; p != end; ++p)
    {
      LOG ("find conflict: lit %s", LOGLIT (*p));
      const unsigned idx = INDEX (*p);
      const unsigned level = solver->levels[idx];
      if (level > res)
	{
	  res = level;
	  *forced = *p;
	  count = 1;
	}
      else if (level == res)
	{
	  count++;
	}
    }

  LOG ("%d literals on actual conflict level %d, forced: %s", count, res,
       forced && *forced != INVALID ? LOGLIT (*forced) : "no");

  // Move the two highest level literals to the front.
  //
#ifndef NVIRTUAL
  if (!is_temporary_binary (solver, conflict))
#endif
    {
      for (unsigned i = 0; i < 2; i++)
	{

	  const unsigned lit = lits[i];

	  unsigned highest_position = i;
	  unsigned highest_literal = lit;
	  const unsigned idx = INDEX (lit);
	  unsigned highest_level = solver->levels[idx];

	  for (int j = i + 1; j < size; j++)
	    {
	      const int other = lits[j];
	      const unsigned idx_other = INDEX (other);
	      const unsigned tmp = solver->levels[idx_other];
	      if (highest_level >= tmp)
		continue;
	      highest_literal = other;
	      highest_position = j;
	      highest_level = tmp;
	      if (highest_level == res)
		break;
	    }

	  // No unwatched higher assignment level literal.
	  //
	  if (highest_position == i)
	    continue;

#ifndef NWATCHES
	  if (highest_position > 1)
	    {
	      LOGCLS (conflict, "unwatch %d in", lit);
	      unwatch_literal (solver, lit, conflict);
	    }
#endif

	  lits[highest_position] = lit;
	  lits[i] = highest_literal;

#ifndef NWATCHES
	  if (highest_position > 1)
#ifndef NBLOCK
	    watch_literal (solver, conflict->redundant, highest_literal,
			   lits[!i], conflict);
#else
	    watch_literal (solver, highest_literal, conflict);
#endif
#endif
	}
    }


  // Only if the number of highest level literals in the conflict is one
  // then we can reuse the conflict clause as driving clause for 'forced'.
  //
  if (count != 1)
    {
      *forced = UINT32_MAX;
      LOG ("no forcing literal");
    }

  return res;

}

#ifndef NHEAP
unsigned
reuse_scored_trail_from (struct satch *solver, unsigned asserting_level)
{
  unsigned next = max_score_unassigned_variable_on_binary_heap (solver);
  const double *const scores = solver->scores[solver->stable].score;
  struct clause *const *const reasons = solver->reasons;
  struct control const control = solver->control;
  unsigned *const end = solver->trail.end;
  const double next_score = scores[next];
  double decision_score = MAX_SCORE;
  const unsigned control_position =
    asserting_level ? asserting_level - 1 : asserting_level;
  for (unsigned *lit = ACCESS (control, control_position).trail; lit != end;
       ++lit)
    {
      const unsigned idx = INDEX (*lit);
      const double score = scores[idx];
      const unsigned level = solver->levels[idx];
      if (level <= asserting_level)
	continue;
      if (decision_score < score || score < next_score)
	return level - 1;
      if (!reasons[idx])
	decision_score = score;
    }
  return solver->level - 1;
}
#endif

#ifndef NQUEUE
unsigned
reuse_stamped_trail_from (struct satch *solver, unsigned asserting_level)
{
  unsigned next = max_stamped_unassigned_variable_on_decision_queue (solver);
  const struct link *const links = solver->queue[solver->stable].links;
  struct clause *const *const reasons = solver->reasons;
  struct control const control = solver->control;
  unsigned *const end = solver->trail.end;
  const unsigned next_stamp = links[next].stamp;
  unsigned decision_stamp = UINT_MAX;
  const unsigned control_position =
    asserting_level ? asserting_level - 1 : asserting_level;
  for (unsigned *lit = ACCESS (control, control_position).trail; lit != end;
       ++lit)
    {
      const unsigned idx = INDEX (*lit);
      const unsigned stamp = links[idx].stamp;
      const unsigned level = solver->levels[idx];
      if (level <= asserting_level)
	continue;
      if (decision_stamp < stamp || stamp < next_stamp)
	return level - 1;
      if (!reasons[idx])
	decision_stamp = stamp;
    }
  return solver->level - 1;
}
#endif

#endif

#ifndef NCHRONO
#define CHRONOLEVELS 100
#endif

#ifndef NCDCL
// Determine the level we should jump back to. Without chronological backtracking, this is
// simply the asserting level. With it, there are three possibilities:
//    - if backtracking does not make sense (e.g., when vivifying), backjump
//    - otherwise, we use a restart-like heuristic to determine how much should be reused...
//    - ...unless all variables have been decided. Then we jump to the lastest level.
static unsigned
determine_jump_level (struct satch *solver, unsigned conflict_level,
		      unsigned *asserting_level)
{
  signed char *frames = solver->frames;
  unsigned jump_level = 0;
  *asserting_level = 0;

  for (all_elements_on_stack (unsigned, lit_level, solver->blocks))
    {
      frames[lit_level] = 0;
      if (lit_level != conflict_level && *asserting_level < lit_level)
	*asserting_level = lit_level;
#ifndef NCONTROL
      if (lit_level)
	ACCESS (solver->control, lit_level - 1).seen.count = 0,
	  ACCESS (solver->control, lit_level - 1).seen.earliest = UINT32_MAX;
#endif
    }
  LOG ("asserting level: %d", *asserting_level);

#ifndef NCHRONO
  if (solver->level - *asserting_level < CHRONOLEVELS ||
      solver->level - 1 == *asserting_level
#ifndef NVIVIFICATION
      || solver->vivifying
#endif
    )
    {
      LOG ("normal backjumping");
      return *asserting_level;
    }
  LOG ("backjumping considered too inefficient");
  if (!solver->unassigned)
    {
      jump_level = solver->level - 1;
      if (*asserting_level != solver->level - 1)
	{
	  INC (chrono);
	  ADD (chronosaved, jump_level - *asserting_level);
	}
      return jump_level;
    }
#ifndef NCHRONOREUSE
#ifndef NQUEUE
  if (!solver->queue[solver->stable].size)
    return solver->level - 1;
#endif

#if defined(NHEAP)
  jump_level = reuse_stamped_trail_from (solver, *asserting_level);
#elif defined(NQUEUE)
  jump_level = reuse_scored_trail_from (solver, *asserting_level);
#else
  if (solver->stable)
    {
      jump_level = reuse_scored_trail_from (solver, *asserting_level);
    }

  else
    {
      jump_level = reuse_stamped_trail_from (solver, *asserting_level);
    }
#endif
#else // NCHRONOREUSE = always backtrack to lastest level
  jump_level = solver->level - 1;
#endif
  assert (jump_level >= *asserting_level);
  if (*asserting_level != jump_level)
    {
      INC (chrono);
      ADD (chronosaved, jump_level - *asserting_level);
    }

#else // no backtracking
  jump_level = *asserting_level;
#endif
  return jump_level;
}
#endif

#ifdef NCDCL
static void
produce_reason_for_checker (struct satch *solver)
{
  struct clause *const *const reasons = solver->reasons;
  for (unsigned *lit = solver->trail.begin; lit != solver->trail.end; ++lit)
    {
      const unsigned idx = INDEX (*lit);
      if (!reasons[idx])
	{
	  PUSH (solver->clause, NOT (*lit));
	}
    }

  struct averages *a = averages (solver);
  {
    double trail_filled = percent (SIZE_STACK (solver->trail),
				   solver->statistics.remaining);
    update_slow_average (&a->trail_filled, trail_filled);
    update_slow_average (&a->conflict_level, solver->level);
  }
  {
    const uint64_t decisions = DECISIONS;
    const uint64_t delta_decisions = decisions - a->saved_decisions;
    a->saved_decisions = decisions;
    update_slow_average (&a->decision_rate, delta_decisions);
  }
  update_betas (solver);

  trace_and_check_temporary_addition (solver);

  CLEAR_STACK (solver->clause);

}
#endif

// First we deduce the 'first unique implication point' (1st UIP) clause,
// minimize, shrink and learn it, then determine backjump level, backtrack
// and assign the 1st UIP literal to the opposite value with the learned
// clause as reason.  We also update various statistics during the analysis.
static bool
analyze_conflict (struct satch *solver, struct clause *conflict)
{
  assert (!solver->inconsistent);
  assert (EMPTY_STACK (solver->clause));	// Clause learned.

  if (!solver->level)
    {
      LOG ("learned empty clause");
      trace_and_check_empty_addition (solver);
      solver->inconsistent = true;
      return false;
    }

#ifdef NCDCL
  (void) conflict;
  produce_reason_for_checker (solver);
#ifndef NCONTROL
  struct level const *const saved =
    &ACCESS (solver->control, solver->level - 1);
  const unsigned uip = *saved->trail;
  assert (solver->values[uip]);
  assert (saved->lvl == solver->level);
#else
  assert (!EMPTY_STACK (solver->trail));
  unsigned *uipp = solver->trail.end - 1;
  while (solver->reasons[INDEX (*uipp)])
    {
      assert (uipp > solver->trail.begin);
      --uipp;
    }
  const unsigned uip = *uipp;
#endif
#ifndef NTARGET
  if (solver->stable)
    update_phases (solver);
#endif
  unsigned not_uip = NOT (uip);
  backtrack (solver, solver->level - 1);
  LOG ("swapping last decision %s", LOGLIT (uip));
  assert (!solver->values[uip]);
  assign (solver, not_uip, DUMMY_REASON, solver->level == 0);

  return true;
#else
  assert (EMPTY_STACK (solver->blocks));	// Decision levels analyzed.
  assert (EMPTY_STACK (solver->analyzed));	// Analyzed literals.

  PUSH (solver->clause, INVALID);	// Reserve room for 1st UIP.

#ifndef NCHRONO
  unsigned forced = INVALID;
  unsigned *forcedp = &forced;
  const unsigned conflict_level =
    find_conflict_level (solver, conflict, forcedp);
  if (!conflict_level)
    {
      LOG ("learned empty clause");
      trace_and_check_empty_addition (solver);
      solver->inconsistent = true;
      return false;
    }
  if (*forcedp != INVALID)
    {
      assert (solver->values[*forcedp] < 0);
#ifndef NBLOCK
      assert (!is_tagged_clause (conflict));
#endif
      LOG ("missed propagation of lit %s from level %d", LOGLIT (*forcedp),
	   conflict_level);
      backtrack (solver, conflict_level - 1);
#ifndef NBLOCK
      if (is_temporary_binary (solver, conflict) || conflict->size == 2)
	{
#ifndef NBLOCK
	  unsigned other =
	    *forcedp ^ conflict->literals[0] ^ conflict->literals[1];
	  struct clause *reason = tag_binary_clause (true, other);
	  assign (solver, *forcedp, reason, false);
#else
	  assign (solver, *forcedp, conflict, false);
#endif
	}
      else
#endif
	assign (solver, *forcedp, conflict, false);
      CLEAR_STACK (solver->blocks);
      CLEAR_STACK (solver->clause);
      assert (solver->level == conflict_level - 1);
      return true;
    }
  if (conflict_level < solver->level)
    {
      LOG ("conflict was on level %d instead of current level %d",
	   conflict_level, solver->level);
      backtrack (solver, conflict_level);
    }
  else
    {
      LOG ("conflict is on current level");
    }
#else
  const unsigned conflict_level = solver->level;
#endif
  signed char *const marks = solver->marks;
  const unsigned *const levels = solver->levels;
  struct clause *const *const reasons = solver->reasons;
  signed char *frames = solver->frames;

  struct clause *reason = conflict;

  const unsigned *t = solver->trail.end;
  unsigned unresolved_on_current_level = 0;
  unsigned uip = INVALID;

  uint64_t ticks = 0;

  for (;;)
    {
      assert (reason);
      LOGCLS (reason, "analyzing");
#ifndef NUSED
#ifndef NBLOCK
      if (!is_temporary_binary (solver, reason))
#endif
	{
	  assert (uip == INVALID || solver->values[uip] > 0);
	  if (!reason->used)
	    reason->used = 1;
#ifndef NTIER2
	  else if (reason->glue <= tier2_glue_limit)
	    reason->used = 2;
#endif
	  ticks++;
	}
#endif
      for (all_literals_in_clause (lit, reason))
	{
	  if (lit == uip)
	    continue;
	  const unsigned lit_level = analyze_literal (solver, lit);
	  if (lit_level == INVALID)
	    continue;
	  assert (solver->values[lit] < 0);
	  if (lit_level < conflict_level)
	    {
	      if (!frames[lit_level])
		{
		  LOG ("analyzing decision level %u", lit_level);
		  PUSH (solver->blocks, lit_level);
		  frames[lit_level] = 1;
		}
	      PUSH (solver->clause, lit);
#ifndef NCONTROL
	      const unsigned idx = INDEX (lit);
	      const unsigned level = solver->levels[idx];
	      if (level != 0)
		{
		  struct level *saved = &ACCESS (solver->control, level - 1);
		  if (saved->seen.earliest > solver->position[idx])
		    saved->seen.earliest = solver->position[idx];
		  ++saved->seen.count;
		  LOG ("updating level %d with: %d %d", level,
		       saved->seen.earliest, saved->seen.count);
		}
#endif
	    }
	  else
	    unresolved_on_current_level++;
	}
      unsigned uip_idx;
      do
	{
	  assert (solver->trail.begin < t);
#ifndef NCHRONO
	  if (solver->levels[INDEX (*--t)] == solver->level)
	    uip = *t;
	  else
	    uip = INVALID;
#else
	  uip = *--t;
#endif
	}
      while (uip == INVALID || !marks[uip_idx = INDEX (uip)]);
      LOG ("next lit to analyze is %s", LOGLIT (uip));
      if (!--unresolved_on_current_level)
	break;
      reason = reasons[uip_idx];
#ifndef NBLOCK
      if (is_tagged_clause (reason))
	reason = untag_clause (solver, 0, uip, reason);
#endif
    }
  assert (uip != INVALID);
  LOG ("first unique implication point %s (1st UIP)", LOGLIT (uip));
  const unsigned not_uip = NOT (uip);
  ACCESS (solver->clause, 0) = not_uip;
  ADD (ticks, ticks);

  LOGTMP ("deduced");
  unsigned size = SIZE_STACK (solver->clause);
  ADD (deduced, size);
  assert (size);

#ifndef NSORTDEDUCED
  sort_deduced_clause (solver);
#endif

#ifndef NMINIMIZE
  START_IF_NCHEAP (minishrink);
#ifndef NSHRINK
  shrink_deduced_clause (solver);
#else
  minimize_deduced_clause (solver);
#endif
  reset_removable_and_poisoned (solver);
  STOP_IF_NCHEAP (minishrink);
  size = SIZE_STACK (solver->clause);
#endif

  const unsigned glue = SIZE_STACK (solver->blocks);
  unsigned asserting_level = 0;
  unsigned jump_level =
    determine_jump_level (solver, conflict_level, &asserting_level);
  CLEAR_STACK (solver->blocks);

  {
    struct averages *a = averages (solver);
#ifndef NRESTART
    update_fast_average (&a->fast_glue, glue);
#endif
    update_slow_average (&a->slow_glue, glue);
    update_slow_average (&a->conflict_level, conflict_level);
    {
      const uint64_t decisions = DECISIONS;
      const uint64_t delta_decisions = decisions - a->saved_decisions;
      a->saved_decisions = decisions;
      update_slow_average (&a->decision_rate, delta_decisions);
    }
    {
      double trail_filled = percent (SIZE_STACK (solver->trail),
				     solver->statistics.remaining);
      update_slow_average (&a->trail_filled, trail_filled);
    }
    update_betas (solver);

    LOG ("determined jump level %u and glue %u", jump_level, glue);
    LOG ("exponential 'conflict_level' moving average %g",
	 unbiased_slow_average (a, a->conflict_level));
#ifndef NRESTART
    LOG ("exponential 'fast_glue' moving average %g",
	 unbiased_fast_average (a, a->fast_glue));
#endif
    LOG ("exponential 'slow_glue' moving average %g",
	 unbiased_slow_average (a, a->slow_glue));
  }

#ifndef NBUMPREASONS
  bump_reason_side_literals (solver);
#endif

#ifndef NSORTANALYZED
#ifndef NVSIDS
  if (!solver->stable)
#endif
    sort_analyzed (solver);	// Sort analyzed variables on time stamp.
#endif

  for (all_elements_on_stack (struct analyzed, analyzed, solver->analyzed))
    {
      const unsigned idx = analyzed.idx;
#if !defined(NVMTF) || !defined(NVSIDS)
#ifndef NBUMP
      INC (bumped);
#if defined(NVMTF) || defined(NQUEUE)
      bump_variable_score (solver, idx);
#elif defined(NVSIDS) || defined(NHEAP)
      move_variable_to_front (solver, idx);
#else
      if (solver->stable)
	bump_variable_score (solver, idx);
      else
	move_variable_to_front (solver, idx);
#endif
#endif
#endif
      assert (marks[idx]);
      marks[idx] = 0;
    }
  CLEAR_STACK (solver->analyzed);

#ifndef NVSIDS
#ifndef NSWITCH
  if (solver->stable)
#endif
    bump_score_increment (solver);
#endif

  trace_and_check_temporary_addition (solver);

#ifndef NTARGET
  assert (solver->level);
  backtrack (solver, solver->level - 1);
  if (solver->stable)
    update_phases (solver);
  if (jump_level < solver->level)
#endif
    backtrack (solver, jump_level);

  if (size == 1)		// Learned a unit clause.
    {
#ifdef NCHRONO
      assert (!jump_level);
#endif
      solver->iterate = true;
      assign (solver, not_uip, 0, true);
    }
#ifndef NVIRTUAL
  else if (size == 2)
    {
      const unsigned other = ACCESS (solver->clause, 1);
      LOGBIN (true, not_uip, other, "learned");
#ifndef NLEARN
      add_new_binary_and_watch_it (solver, true);
#endif
      ADD (learned, 2);
      struct clause *reason = tag_binary_clause (true, other);
      assign (solver, not_uip, reason, false);
    }
#endif
  else
    {
      assert (size > 1);	// Learned and at least binary clause.
      assert (jump_level > 0);

      // First literal at jump-level becomes other watch.  Such a literal
      // has to exist and thus the 'break' below has to be hit.  We further
      // rely on backtracking not to reset the level of unassigned literals.
      for (unsigned *p = solver->clause.begin + 1, *q = p;; q++)
	{
	  assert (q != solver->clause.end);
	  const unsigned lit = *q;
	  unsigned idx = INDEX (lit);
	  unsigned lit_level = levels[idx];
	  assert (lit_level <= asserting_level);
	  if (lit_level == asserting_level)
	    {
	      *q = *p;
	      *p = lit;
	      break;
	    }
	}

#ifndef NGLUE
      struct clause *learned = new_redundant_clause (solver, glue);
#else
      struct clause *learned = new_redundant_clause (solver);
#endif

#ifndef NUSED
#ifndef NTIER2
      if (glue <= tier2_glue_limit)
	learned->used = 2;
      else
#endif
	learned->used = 1;
#endif
      LOGCLS (learned, "learned");
      ADD (learned, size);
#ifndef NLEARN
#ifndef NWATCHES
      watch_clause (solver, learned);
#else
      connect_clause (solver, learned);
      count_clause (solver, learned);
#endif
#endif
      assign (solver, not_uip, learned, false);
    }

  CLEAR_STACK (solver->clause);
  return true;
#endif
}
