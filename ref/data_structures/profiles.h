// *INDENT-OFF*
#define PROFILES \
PROFILE_IF_FOCUSED (focused)     /* Time spent in focused mode. */ \
PROFILE_IF_ELIMINATION (eliminate) /* Time spent in elimination. */ \
PROFILE (parse)                  /* Time spent parsing. */ \
PROFILE_IF_REDUCE (reduce)       /* Time spent reduce. */ \
PROFILE (solve)                  /* Time spent solving. */ \
PROFILE_IF_STABLE (stable)       /* Time spent in stable mode. */ \
PROFILE_IF_SUBSUMPTION (subsume) /* Time spent in full subsumption. */ \
PROFILE_IF_NCHEAP (decide)	 /* Total time deciding. */ \
PROFILE_IF_NCHEAP (minishrink)	 /* Total time minimizing and shrinking. */ \
PROFILE_IF_VIVIFICATION (vivify) /* Time spent in vivification */ \
PROFILE (total)			 /* Total time spent. */

#define DO_NOT_PROFILE(ARG) /**/

#ifndef NFOCUSED
#define PROFILE_IF_FOCUSED PROFILE
#else
#define PROFILE_IF_FOCUSED DO_NOT_PROFILE
#endif

#ifndef NREDUCE
#define PROFILE_IF_REDUCE PROFILE
#else
#define PROFILE_IF_REDUCE DO_NOT_PROFILE
#endif

#ifndef NSTABLE
#define PROFILE_IF_STABLE PROFILE
#else
#define PROFILE_IF_STABLE DO_NOT_PROFILE
#endif

#ifndef NSUBSUMPTION
#define PROFILE_IF_SUBSUMPTION PROFILE
#else
#define PROFILE_IF_SUBSUMPTION DO_NOT_PROFILE
#endif

#ifndef NELIMINATION
#define PROFILE_IF_ELIMINATION PROFILE
#else
#define PROFILE_IF_ELIMINATION DO_NOT_PROFILE
#endif

#ifndef NVIVIFICATION
#define PROFILE_IF_VIVIFICATION PROFILE
#else
#define PROFILE_IF_VIVIFICATION DO_NOT_PROFILE
#endif

#ifndef DNCHEAPPROFILING
#define PROFILE_IF_NCHEAP PROFILE
#define START_IF_NCHEAP START
#define STOP_IF_NCHEAP STOP
#else
#define PROFILE_IF_NCHEAP DO_NOT_PROFILE
#define START_IF_NCHEAP (A)
#define STOP_IF_NCHEAP (A)
#endif

// *INDENT-ON*

struct profile
{
  double start, time;		// Start time, and total time.
  const char *name;		// Used in 'print_profiles'.
};				// Initialized in 'init_profiles'.

#define MAX_PROFILES            16

struct profiles
{
#define PROFILE(NAME) \
  struct profile NAME;		// Declare all the profiles.
  PROFILES
#undef PROFILE
  struct profile *begin[MAX_PROFILES];	// Pre-allocated!
  struct profile **end;
};

