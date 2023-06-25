/*------------------------------------------------------------------------*/

// Conflict and other limits for restarts, reductions etc.

// We use the following idiom to define an internal macro option 'NLIMITS'
// (i.e., which is not in 'features.h') in case the 'limits' structure
// becomes empty and it does not need to be declared in the solver.  There
// we can then only test 'NLIMITS'.  Note that, an empty 'struct' would
      // trigger an error during pedantic compilation ('./configure -p').

#ifdef NLIMITS
#undef NLIMITS			// This is actually an option thus undefine it first.
#endif

#ifdef NELIMINATION
#ifdef NREDUCE
#ifdef NREPHASE
#ifdef NRESTART
#ifdef NSUBSUMPTION
#ifdef NSWITCH
#ifdef NVIVIFICATION
#define NLIMITS
#endif
#endif
#endif
#endif
#endif
#endif
#endif

#ifndef NLIMITS

struct limits
{
#ifndef NELIMINATION
  struct
  {
    uint64_t conflicts;		// Conflict-limit on elimination.
    uint64_t fixed;		// Root-level fixed at elimination.
    uint64_t marked;		// Marked as elimination candidates.
#ifndef NELIMINATIONLIMITS
    uint64_t ticks;		// Ticks limit for elimination.
    uint64_t search;		// Saved search ticks at last elimination.
#endif
  } eliminate;
#endif
#ifndef NVIVIFICATION
  struct {
    uint64_t conflicts; // Conflict-limit on elimination.
#ifndef NVIVIFICATIONLIMITS
    uint64_t ticks;  // Ticks limit for elimination.
    uint64_t search; // Saved search ticks at last elimination.
#endif
  } vivify;
#endif
#ifndef NREDUCE
  struct
  {
    uint64_t conflicts;		// Conflict-limit on reducing.
    uint64_t fixed;		// Root-level fixed at reduction.
  } reduce;
#endif
#ifndef NREPHASE
  uint64_t rephase;		// Conflict-limit on rephasing.
#endif
#ifndef NRESTART
  uint64_t restart;		// Conflict-limit on restarting.
#endif
#ifndef NSWITCH
  struct
  {
    uint64_t conflicts;		// Conflict-limit if non zero.
    struct
    {
      uint64_t limit;		// Ticks-limit on mode switching.
      uint64_t interval;	// Ticks-mode base-interval (computed).
    } ticks;
  } mode;
#endif
#ifndef NSUBSUMPTION
  struct
  {
    uint64_t marked;		// Marked as subsume candidates.
#ifndef NSUBSUMPTIONLIMITS
    uint64_t ticks;		// Ticks limit for subsumption.
    uint64_t search;		// Saved search ticks at last elimination.
#endif
  } subsume;
#endif
};

#endif

/*------------------------------------------------------------------------*/

#if defined(NVIRTUAL) || defined(NELIMINATION)
#define NBINARIES
#endif

/*------------------------------------------------------------------------*/

// These are counters used for 'reluctant doubling' which is the way how
// Donald Knuth implements the computation of the 'Luby' sequence to control
// restart intervals. We only control restarts through reluctant doubling in
// stable mode though.

// Again we use this idiom explained above to define an internal macro
// option 'NRELUCTANT' which is defined if (through disabling other
// features) there is no need for reluctant doubling code.

#if defined(NRESTART) || defined(NSTABLE)
#define NRELUCTANT
#endif

#ifndef NRELUCTANT

struct reluctant
{
  uint64_t u, v;
};

#endif

