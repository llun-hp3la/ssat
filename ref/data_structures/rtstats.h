/*------------------------------------------------------------------------*/

// Runtime statistics.

struct statistics
{
#ifndef NLAZYACTIVATION
  uint64_t activated[2];	// Activated variables (added queue/scores).
#endif
  uint64_t added;		// Number of added clauses.
#ifndef NBEST
  uint64_t bests;		// Number of saved best trails.
#endif
#ifndef NBUMP
  uint64_t bumped;		// Bumped literals.
#endif
  uint64_t collected;		// Garbage collected bytes.
  uint64_t conflicts;		// Total number of conflicts.
  uint64_t deleted;		// Number of deleted clauses.
  uint64_t decisions;		// Total number of decisions.
  uint64_t deduced;		// Deduced literals (of 1st UIP clause).
#ifndef NELIMINATION
  uint64_t eliminated;		// Number of eliminated variables.
  uint64_t elimination_ticks;	// Number of elimination ticks.
  uint64_t eliminations;	// Number of elimination phases.
#endif
#ifdef NLAZYACTIVATION
  uint64_t filled[2];		// Filled variables (added queue/scores).
#endif
  uint64_t fixed;		// Root level assigned variables (units).
#ifndef NVSIDS
  uint64_t incremented;		// Bumped by incrementing score.
#endif
  uint64_t irredundant;		// Current number of irredundant clauses.
  uint64_t learned;		// Learned literals (after minimization).
#ifndef NELIMINATION
  uint64_t marked_eliminate;	// Marked eliminate candidate variables.
#endif
#ifndef NSUBSUMPTION
  uint64_t marked_subsume;	// Marked subsume candidate variables.
#endif
#ifndef NMINIMIZE
  uint64_t minimized;		// Minimized literals.
#endif
#ifndef NVMTF
  uint64_t moved;		// Bumped by moving to front.
#endif
  uint64_t propagations;	// Propagated literals.
#ifndef NBUMPREASONS
  uint64_t reasons;		// Additionally bumped reason side literals.
#endif
#ifndef NELIMINATION
  uint64_t resolutions;		// Number of resolutions.
#endif
#ifndef NREDUCE
  uint64_t reduced;		// Number of reduced clauses.
  uint64_t reductions;		// Number of reductions (not clauses).
#endif
  uint64_t redundant;		// Current number of redundant clauses.
  uint64_t remaining;		// Remaining active variables.
#ifndef NREPHASE
  uint64_t rephased;		// How often saved phases have been reset.
#endif
  uint64_t reported;		// Number of calls to 'report'.
#ifndef NVSIDS
  uint64_t rescored;		// Rescored EVSIDS scores.
#endif
#ifndef NVMTF
  uint64_t restamped;		// Restamped VMTF timestamps.
#endif
#ifndef NRESTART
  uint64_t restarts;		// Number of restarts.
#endif
#ifndef NREUSE
  uint64_t reused;		// Number of reused trails.
#endif
  uint64_t sections;		// Number of calls to 'section'.
#ifndef NSHRINK
  uint64_t shrunken;		// Shrunken literals.
#endif
  uint64_t solved;		// Number of calls to 'satch_solve'.
#ifndef NSUBSUMPTION
  uint64_t strengthened;	// Strengthened clauses.
  uint64_t subsumption_ticks;	// Number of subsumption ticks.
  uint64_t subsumptions;	// Full backward subsumptions.
#endif
#if !defined (NSUBSUMPTION) || !defined (NVIVIFICATION)
  uint64_t subsumed;            // Subsumed clauses.
#endif
#ifndef NSWITCH
  uint64_t switched;		// Number of focused/stable mode switches.
#endif
#ifndef NTARGET
  uint64_t targets;		// Number of saved target trails.
#endif
#ifndef NCHRONO
  uint64_t chrono;              // Number of chronological backjumping
  uint64_t chronosaved;         // Saved repropagation
  				// during chronological backjumping.
#endif
  uint64_t ticks;		// Propagation ticks.
  uint64_t variables;		// Activated variables.
#ifndef NVIVIFICATION
  uint64_t vivify_reused;
  uint64_t vivify_probes;
  uint64_t vivify_strengthened;
  uint64_t vivify_subsume;
  uint64_t vivified;
  uint64_t vivifications;
  uint64_t vivify_implied;
  uint64_t vivify_conflicts;
  uint64_t probing_ticks;       // Number of elimination ticks.
  uint64_t vivify_propagations;	// Propagated literals.
#endif
};

