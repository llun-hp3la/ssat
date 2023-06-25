/*------------------------------------------------------------------------*/

// We have fast and slow-moving exponential averages, all updated during
// conflict clause analysis.  The slow moving averages are biased towards
// their initial value (zero) and we use a method described in the
// literature (the well known ADAM machine learning paper) to correct the
// bias by multiplying with '1/(1-beta^n)' where 'beta = 1 - alpha' and
// 'beta' is the smoothing factor (decay) and 'n' is the number of updates
// to the exponential moving average.  The alphas are defined above as
// macros since some compilers will otherwise not allow the following line.

const double slow_beta = 1.0 - slow_alpha;

// We have two sets of independent averages for stable and focused mode.
// During mode switching the 'stable' bit is flipped which makes the other
// set of averages active.  However if stable mode is disabled we only have
// one set of averages and only update and use that.  To hide this logic we
// use the following function which returns the active set of averages.

static struct averages *
averages (struct satch *solver)
{
  return solver->averages + solver->stable;
}

static void
update_slow_average (double *average, unsigned value)
{
  *average += slow_alpha * (value - *average);
}

static double
unbiased_slow_average (struct averages *a, double avg)
{
  const double div = 1 - a->slow_exp;
  return !div ? 0 : div == 1 ? avg : avg / div;
}

#ifndef NRESTART

// Only 'restarting' needs a fast moving average ('fast_glue').

const double fast_beta = 1.0 - fast_alpha;

static void
update_fast_average (double *average, unsigned value)
{
  *average += fast_alpha * (value - *average);
}

static double
unbiased_fast_average (struct averages *a, double avg)
{
  const double div = 1 - a->fast_exp;
  return !div ? 0 : div == 1 ? avg : avg / div;
}

#endif

// We assume that all fast and slow moving averages are updated at the same
// time and then just update 'beta^n' for both too (even though there is a
// fast one and a slow one).

static void
update_betas (struct satch *solver)
{
  struct averages *a = averages (solver);
#ifndef NRESTART
  if (a->fast_exp)
    a->fast_exp *= fast_beta;
#endif
  if (a->slow_exp)
    a->slow_exp *= slow_beta;
}

static void
init_one_set_of_averages (struct averages *a)
{
  a->slow_exp = 1.0;
#ifndef NRESTART
  a->fast_exp = 1.0;
#endif
}

static void
init_averages (struct satch *solver)
{
  for (int i = 0; i < 2; i++)
    init_one_set_of_averages (&solver->averages[i]);
}

