/*------------------------------------------------------------------------*/

// Restarts are in principle triggered by restart intervals (measured in the
// number of conflicts passed).  However in focused mode we use exponential
// moving averages of the glucose level (glue) of learned clauses to
// determine whether we are in a phase where those levels go down or
// increase.  If the glue goes down we do not restart but if it goes up,
// that is the fast moving average is above a certain margin over the slower
// moving average, then we restart.

#ifndef NRESTART

static bool
restarting (struct satch *solver)
{
  assert (solver->unassigned);
  assert (!solver->inconsistent);

  if (!solver->level)
    return false;
  if (solver->limits.restart > CONFLICTS)
    return false;

#ifndef NSTABLE

  // Use only (large) conflict intervals in stable mode to trigger restarts.
  // However during computing the next restart limit below we use reluctant
  // doubling of the base restart interval (also called 'Luby' scheme).

  if (solver->stable)
    return true;

#endif

  struct averages *a = averages (solver);

  const double fast = unbiased_fast_average (a, a->fast_glue);
  const double slow = unbiased_slow_average (a, a->slow_glue);
  const double limit = restart_margin * slow;

  return limit <= fast;
}

static void
restart (struct satch *solver)
{
  const uint64_t restarts = INC (restarts);
  message (solver, 4, "restart", restarts,
	   "restarting after %" PRIu64 " conflicts (limit %" PRIu64 ")",
	   CONFLICTS, solver->limits.restart);
  report (solver, 3, 'r');

#ifndef NTARGET
  if (solver->stable)
    update_phases (solver);
#endif

#ifndef NREUSE
  {
    unsigned new_level = reuse_trail (solver);
    if (new_level < solver->level)
      backtrack (solver, new_level);
  }
#else
  backtrack (solver, 0);
#endif

  uint64_t interval;
#ifndef NSTABLE
  if (solver->stable)
    {
      // This is the approach of Donald Knuth to compute the 'reluctant
      // doubling' sequence. In other solvers it is called 'Luby' sequence.
      // We further use a much longer base interval than in focused mode.

      struct reluctant *r = &solver->reluctant;
      uint64_t u = r->u, v = r->v;

      // The base interval is multiplied with the reluctant doubling
      // sequence number (1,2,1,1,2,4,1,1,2,4,8,1,1,2,1,1,2,4,1,1,...).

      interval = v * stable_restart_interval;

      if ((u & -u) == v)
	u++, v = 1;
      else
	assert (UINT64_MAX / 2 >= v), v *= 2;
      r->u = u, r->v = v;
    }
  else
#endif
    {
      assert (restart_interval >= 1);
      interval = (restart_interval - 1) + logn (restarts);
      assert (restart_interval <= interval);
    }

  solver->limits.restart = CONFLICTS + interval;

  message (solver, 4, "restart", restarts,
	   "new %s restart limit %" PRIu64 " after %" PRIu64 " conflicts",
	   solver->stable ? "stable" : "focused",
	   solver->limits.restart, interval);
}

#endif

