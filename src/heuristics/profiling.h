/*------------------------------------------------------------------------*/

// Macros and functions to 'START' and 'STOP' profiling a function.

// References to profiles are pushed on the profile stack in order to
// include time spent in a function in case that function is interrupted
// ('START' issued but interrupted without the corresponding 'STOP').

// Having this profiling information printed in optimized code running on a
// full set of benchmarks is very important to find performance regressions.

#define START(NAME) \
  start_profiling (solver, &solver->profiles.NAME)

#define STOP(NAME) \
  stop_profiling (solver, &solver->profiles.NAME, process_time ())

static void
init_profiles (struct satch *solver)
{
  struct profiles *profiles = &solver->profiles;
  profiles->end = profiles->begin;
#define PROFILE(NAME) \
  profiles->NAME.name = #NAME;
  PROFILES
#undef PROFILE
}

static void
start_profiling (struct satch *solver, struct profile *profile)
{
  struct profiles *profiles = &solver->profiles;
  const double start = process_time ();
  profile->start = start;
  assert (profiles->end < profiles->begin + MAX_PROFILES);
  *profiles->end++ = profile;
}

// Starting and stopping a profile has to follow a block structure, i.e.,
// the corresponding 'STOP' has be to called in reverse order of 'START'.

// For instance 'START (A); START (B); ...; STOP (B); STOP (A);' is correct
// but interleaving not ('START (A); START (B); ...; STOP (A); STOP (B);').

// In order to simplify testing and debugging violations of this rule we
// explicitly ask the caller to specify the stopped profile, even though in
// principle it could be derived from the top of the profile stack.

static double
stop_profiling (struct satch *solver, struct profile *profile, double stop)
{
  struct profiles *profiles = &solver->profiles;
  assert (TOP (*profiles) == profile);
  const double time = stop - profile->start;
  profile->time += time;
  (void) POP (*profiles);
  return time;
}

// If interrupted, flush all pending unfinished profiles with the current
// process time.  In order to avoid calling 'getrusage' too often in this
// (often critical and time-constrained) situation we have the current time
// as argument to 'stop_profiling'.

static double
flush_profiles (struct satch *solver)
{
  struct profiles *profiles = &solver->profiles;
  const double stop = process_time ();
  while (!EMPTY_STACK (*profiles))
    stop_profiling (solver, TOP (*profiles), stop);
  profiles->total.time = profiles->parse.time + profiles->solve.time;
  return stop;
}

// Printing the profile information first sorts them according to time.

// We use our own bubble-sort since, first, the number of profiles is small
// and more importantly we do not want to allocate heap memory (usually
// required by implementations of 'qsort') because this function should only
// work with already existing memory.

// Consider for instance the case where it was called from an interrupt
// handler catching a segmentation-fault due to out-of-memory.  Then calling
// an external sorting function might trigger another segmentation-fault and
// we will not see the profiling information.  This is bad because for an
// out-of-memory run the profiling information might be particularly useful.

static double
print_profiles (struct satch *solver)
{
  // First flush all timing information (stop all pending profiles).

  const double stop = flush_profiles (solver);

  internal_section (solver, "profiling");	// As early as possible.

  // Then add all profiles to the (pre-allocated) profiles stack skipping
  // those without any time spent in it (unless verbose level is larger 1).

  struct profiles *profiles = &solver->profiles;
  const bool verbose = solver->options.verbose > 1;
  assert (EMPTY_STACK (*profiles));

// *INDENT-OFF*

#define PROFILE(NAME) \
do { \
    struct profile * profile = &profiles->NAME; \
    if (profile == &profiles->total) \
      break; \
    if (!verbose && !profile->time) \
      break; \
    assert (profiles->end < profiles->begin + MAX_PROFILES); \
    *profiles->end++ =  &profiles->NAME; \
} while (0);

  PROFILES
#undef PROFILE

// *INDENT-ON*

  // Sort profiles with respect to time used and name as tie breaker.

  const size_t size = SIZE_STACK (*profiles);
  for (size_t i = 0; i < size; i++)
    {
      struct profile *p = profiles->begin[i];
      for (size_t j = i + 1; j < size; j++)
	{
	  struct profile *q = profiles->begin[j];
	  if (p->time < q->time ||
	      (p->time == q->time && strcmp (p->name, q->name) > 0))
	    {
	      profiles->begin[i] = q;
	      profiles->begin[j] = p;
	      p = q;
	    }
	}
    }

  // Finally print the profile information in sorted order.

  const double total = profiles->total.time;
  for (size_t i = 0; i < size; i++)
    {
      struct profile *p = profiles->begin[i];
      printf ("c %14.2f  %6.2f %%  %s\n",
	      p->time, percent (p->time, total), p->name);

    }
  fputs ("c =============================================\n", stdout);
  printf ("c %14.2f  %6.2f %%  total\n", total, 100.0);

  return stop;
}

