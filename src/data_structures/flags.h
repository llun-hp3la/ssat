// Variable flags.

struct flags
{
  bool active:1;		// Active so neither fixed nor eliminated.
#ifndef NELIMINATION
  bool eliminate:1;		// Removed since last 'eliminate'.
  bool eliminated:1;		// Variable eliminated in 'eliminate'.
#endif
  bool fixed:1;			// Root-level assigned variable (unit).
#ifndef NSUBSUMPTION
  unsigned subsume:2;		// Newly added after last 'subsume'.
#endif
};

