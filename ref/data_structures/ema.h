/*------------------------------------------------------------------------*/

// Exponential moving averages (for 'exp' see below).

struct averages
{
  double conflict_level;	// Slow moving average of conflict level.
  double slow_glue;		// Slow moving average of glue.
  double slow_exp;		// Cached 'slow_beta^n'.
  double trail_filled;		// Slow moving relative trail size average.
  double decision_rate;		// Slow decisions per conflict rate.
  uint64_t saved_decisions;
#ifndef NRESTART
  double fast_glue;		// Fast moving average of glue.
  double fast_exp;		// Cached 'fast_beta^n'.
#endif
};

