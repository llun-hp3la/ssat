/*------------------------------------------------------------------------*/

// Switch between focused mode with aggressive restarting and stable mode
// with almost no restarting.  At the same time switch between two different
// decision variable schemes (by default VMTF vs (E)VSIDS).  During stable
// mode we also enable rephasing and target phases.  The two modes have
// separate averages ('glue', 'rate', 'level' and 'trail').

// Starting and ending a mode is indicated by a '{' and '}' pair for focused
// mode (the initial mode) and '[' and ']' for stable mode.

#ifndef NSWITCH

static void
start_mode (struct satch *solver)
{
  if (solver->stable)
    {
      START (stable);
      report (solver, 1, '[');
      LOG ("start stable mode");
    }
  else
    {
      START (focused);
      report (solver, 1, '{');
      LOG ("start focused mode");
    }
}

static void
stop_mode (struct satch *solver)
{
  if (solver->stable)
    {
      STOP (stable);
      LOG ("stop stable mode");
      report (solver, 1, ']');
    }
  else
    {
      STOP (focused);
      LOG ("stop focused mode");
      report (solver, 1, '}');
    }
}

// Initially (for the first focused mode phase) we use a non-zero conflict
// limit ('initial_mode_conflicts_interval') and then compute the number of
// 'ticks' spent in this first mode.  This is then used as base ticks
// interval for the length of the remaining mode phases.

// To indicate that we moved to a ticks based limits we set
// 'limits->mode.conflicts' to zero after the first mode switch.
// Accordingly when testing for switching we first check whether that is
// zero and then use ticks instead of conflicts.

// As you can see we still use a ticks limit for the first round since we
// encountered cases were relying on conflicts only took too much time.

static bool
switching (struct satch *solver)
{
  struct limits *limits = &solver->limits;
  if (limits->mode.conflicts && limits->mode.conflicts <= CONFLICTS)
    return true;
  return limits->mode.ticks.limit <= TICKS;
}

static void
set_new_mode_switching_limit (struct satch *solver, uint64_t switched)
{
  struct limits *limits = &solver->limits;
  const uint64_t interval = limits->mode.ticks.interval;
  const uint64_t count = (switched + 1) / 2;
  const uint64_t scaled = scale_interval (interval, quadratic, count);
  solver->limits.mode.ticks.limit = TICKS + scaled;
  message (solver, 3, "switch", switched,
	   "new %s mode limit of %" PRIu64 " ticks after %" PRIu64 " ticks",
	   solver->stable ? "focused" : "stable",
	   limits->mode.ticks.limit, scaled);
}

static void
mode_ticks_limit_hit (struct satch *solver, uint64_t switched)
{
  message (solver, 2, "switch", switched,
	   "limit of %" PRIu64 " ticks hit at %" PRIu64 " ticks",
	   solver->limits.mode.ticks.limit, TICKS);
}

static void
switch_to_focused_mode (struct satch *solver, uint64_t switched)
{
  assert (solver->stable);
  mode_ticks_limit_hit (solver, switched);
  solver->stable = false;
  assert (switched >= 2);
  assert (!(switched & 1));
}

static void
switch_to_stable_mode (struct satch *solver, uint64_t switched)
{
  assert (!solver->stable);

  struct limits *limits = &solver->limits;

  if (limits->mode.conflicts)
    {
      message (solver, 2, "switch", switched,
	       "limit of %" PRIu64 " conflicts hit at %"
	       PRIu64 " conflicts and %" PRIu64 " ticks",
	       limits->mode.conflicts, CONFLICTS, TICKS);

      limits->mode.ticks.interval = TICKS;
      limits->mode.conflicts = 0;
    }
  else
    mode_ticks_limit_hit (solver, switched);

  solver->stable = true;
  assert ((switched & 1));

#ifndef NRESTART
  solver->reluctant.u = solver->reluctant.v = 1;
  solver->limits.restart = CONFLICTS + stable_restart_interval;
#endif

#ifndef NTARGET
  LOG ("reset target size");
  solver->target = 0;
#endif
}

static void
switch_mode (struct satch *solver)
{
  stop_mode (solver);
  const uint64_t switched = INC (switched);

  // Make sure to push back all assigned variables to the scores heap and
  // reset the VMTF queue if there are still variables on the trail.
  // Otherwise the scores heap respectively the queue is not really saved.
  // There is even the danger to violate the invariant that unassigned
  // literals are not all on the binary heap when switching back etc.

  if (solver->level)
    backtrack (solver, 0);

  if (solver->stable)
    switch_to_focused_mode (solver, switched);
  else
    switch_to_stable_mode (solver, switched);

  // Save the number of decisions when entering the new mode to compute the
  // mode specific 'decision rate' exponential moving average.

  struct averages *a = averages (solver);
  a->saved_decisions = DECISIONS;

  set_new_mode_switching_limit (solver, switched);
  start_mode (solver);
}

#endif
