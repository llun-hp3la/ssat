/*------------------------------------------------------------------------*/

// Rephasing is the process of resetting the saved phases of the solver in
// increasing intervals.  It can be seen as a diversification method with
// respect to the selected phases (since phase saving might be considered
// to be too stubborn).  However, in combination with reusing best-phases
// and particularly target-phases it has more an intensification flavor.

// In the past, we experimented with many variants on how to reset phases
// and now reached the following set-up, which seems to give consistent
// improvements. First it seems that rephasing is only beneficial in stable
// mode. Second we only reset to the original, the inverted-original or the
// best-phase seen. Third we schedule rephasing slightly more frequently than
// mode switching, such that for instance initially maybe the phases are
// reset twice in one stable mode interval and then this number increases
// slowly in later stable mode intervals.

// At this point we do not have local search rephasing incorporated yet
// which we do consider to give benefits.  It is also not combined with
// autarky simplification either which allows to save partial satisfying
// assignments. Both are implemented in Kissat and need to be ported.

#ifndef NREPHASE

static bool
rephasing (struct satch *solver)
{
  if (!solver->stable)
    return false;
  return solver->limits.rephase <= CONFLICTS;
}

static char
original_phases (struct satch *solver)
{
  const signed char value = original_phase ();
  memset (solver->saved, value, VARIABLES);
  return 'O';
}

#ifndef NINVERTED

static char
inverted_phases (struct satch *solver)
{
  const signed char value = -original_phase ();
  memset (solver->saved, value, VARIABLES);
  return 'I';
}

#endif

#ifndef NBEST

static char
best_phases (struct satch *solver)
{
  const signed char *const bests = solver->bests;
  const signed char *const end = bests + VARIABLES;
  signed char *const saved = solver->saved;
  signed char *q = saved, tmp;
  for (const signed char *p = bests; p != end; p++, q++)
    if ((tmp = *p))
      *q = tmp;
  solver->best = 0;
  return 'B';
}

#endif

static void
rephase (struct satch *solver)
{
  char (*functions[4]) (struct satch *);
  unsigned size_functions = 0;

#ifndef NINVERTED
  functions[size_functions++] = inverted_phases;
#ifndef NBEST
  functions[size_functions++] = best_phases;
#endif
#endif
  functions[size_functions++] = original_phases;
#ifndef NBEST
  functions[size_functions++] = best_phases;
#endif
  assert (size_functions <= sizeof functions / sizeof *functions);

  const uint64_t rephased = INC (rephased);
  const char type = functions[rephased % size_functions] (solver);

  const uint64_t interval =
    scale_interval (rephase_interval, nlognlognlogn, rephased);
  solver->limits.rephase = CONFLICTS + interval;
  message (solver, 4, "rephase", rephased,
	   "new rephase limit %" PRIu64 " conflicts after %" PRIu64,
	   solver->limits.rephase, interval);
#ifndef NTARGET
  if (solver->stable)
    {
      LOG ("reset target size");
      memcpy (solver->targets, solver->saved, VARIABLES);
      solver->target = 0;
    }
#endif
  report (solver, 1, type);
}

#endif

