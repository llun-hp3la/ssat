/*------------------------------------------------------------------------*/
// We use an idiom of defining at compile-time a list of code parameters
// multiple times (here 'PROFILES', but also see 'REPORTS' below and
// 'SIGNALS' in 'main.c').  The idea is that the parameter list contains the
// variations of some common code, that is compile-time parameters of that
// code.  Here for example the common code will be in the 'PROFILE' macro
// (singular) which is then instantiated with its single parameter (we use
// 'NAME') if we just write 'PROFILES' (plural).  This way  we can use that
// parameter in 'PROFILE' at compile time as symbol as well as string (with
// '#NAME'), or even generate new symbols (see 'SIGNALS' in 'main.c').

// The full solver state is captured in this structure.

struct satch
{
  int status;			// UNKNOWN, SATISFIABLE, UNSATISFIABLE.
  bool inconsistent;		// Empty clause found or derived.
  bool iterate;			// Report learned unit clause.
  bool stable;			// Stable mode (fewer restarts).
  bool dense;			// Dense mode (connected - not watched).
  unsigned level;		// Current decision level.
  unsigned size;		// Number of variables.
  size_t capacity;		// Allocated variables.
  unsigned unassigned;		// Number of unassigned variables.
  unsigned *levels;		// Decision levels of variables.
  signed char *values;		// Current assignment of literals.
  struct flags *flags;		// Variable flags.
#ifndef NSAVE
  signed char *saved;		// Saved assignments of variables.
#endif
#ifndef NTARGET
  signed char *targets;		// Target phases.
  unsigned target;		// Maximum trail size.
#endif
#ifndef NBEST
  signed char *bests;		// Best phases.
  unsigned best;		// Best trail size.
#endif
  signed char *marks;		// Mark flags of variables.
#ifndef NLAZYACTIVATION
  struct unsigned_stack put[2];	// To be put on decision queue / heap.
#endif
#ifndef NMINIMIZE
  struct unsigned_stack poisoned;	// Variables marked as poisoned.
  struct unsigned_stack removable;	// Variables marked as removable.
#endif
#ifndef NSHRINK
  struct unsigned_stack shrunken;	// Shrunken variables.
#endif
#ifndef NCONTROL
  unsigned *position;		// Variable position on trail.
#endif
  signed char *frames;		// Level pulled in learned clauses.
#ifndef NQUEUE
  struct queue queue[2];	// Variable decision queue (stable=1).
#endif
#ifndef NHEAP
  struct heap scores[2];	// Variable decision heap (stable=1).
#endif
  struct clause **reasons;	// Reason clauses of a variable.
#ifndef NBLOCK
  struct clause binary[2];	// Temporary binary clauses.
#endif
#ifndef NBINARIES
  struct unsigned_stack binaries;	// Saved redundant binary clauses.
#endif
#ifndef NELIMINATION
  struct unsigned_stack extend;	// Solution reconstruction.
  struct unsigned_stack resolvents;	// Temporary resolvents.
#endif
  struct watches *watches;	// Watches of a literal.
  struct trail trail;		// Assigned literals.
#ifndef NCONTROL
  struct control control;	// control structure
#endif
  struct analyzed_stack analyzed;	// Analyzed literals.
  struct unsigned_stack clause;	// Temporary clause.
  struct unsigned_stack blocks;	// Analyzed decision levels.
  struct clauses irredundant;	// Current irredundant clauses.
  struct clauses redundant;	// Current redundant clauses.
#ifndef NLIMITS
  struct limits limits;		// Limits on restart, reduce, etc.
#endif
#ifndef NRELUCTANT
  struct reluctant reluctant;	// Doubling for stable restart (Luby).
#endif
  struct options options;	// Few runtime options.
  struct averages averages[2];	// Exponential moving averages (stable=1).
  struct statistics statistics;	// Statistic counters.
  struct profiles profiles;	// Built in run-time profiling.
#ifndef NDEBUG
  struct int_stack original;	// Copy of all original clauses.
  struct checker *checker;	// Internal proof checker.
#endif
  struct int_stack added;	// Added external clause.
  FILE *proof;			// Tracing to this file if non-zero.
#ifdef LOGGING
  char format[4][128];		// String buffer for logging.
  unsigned next_format;		// Next buffer for logging.
#endif
#ifndef NVIVIFICATION
  struct unsigned_stack sorted;
  struct unsigned_stack sorter;
  struct clauses vivification_schedule;
  signed char *vivify_marks;	// TODO: make marks compatible with analyzed
  // and mark_literal at the same time.
  bool vivifying;
#ifndef NDEBUG
  bool watching;
#endif
#endif
#ifdef DLIS
  // When running DLIS we save how far the clauses are satisfied to avoid
  // rechecking them. Our implementation is not optimal, since it does not
  // handle chronological backtracking (so clauses will be rechecked several
  // if there are satisfied by a literal set at a lower level.). However,
  // this does not really matter, since you should not use DLIS anyway
  // nowadays (or you need a less lazy SAT solver).
  struct int_stack irred_sat_upto;
  struct int_stack red_sat_upto;
#endif
};
