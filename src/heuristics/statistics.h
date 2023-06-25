/*------------------------------------------------------------------------*/

static void
print_statistics (struct satch *solver, double seconds)
{
  internal_section (solver, "statistics");
  struct statistics s = solver->statistics;
  const bool verbose = solver->options.verbose > 1;

  // Factored out parts of the formatting string.

#define F1 "c %-24s"		// Prefix plus left justified name.
#define L2 "17"			// First number column (absolute values).
#define L3 "17"			// Second number column (absolute values).
#define P3 "14"			// Second number column (relative / percent).

  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 "s clauses\n", "added:", s.added, "");
#ifndef NBEST
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "bests:",
	  s.bests, relative (s.conflicts, s.bests));
#endif
#ifndef NBUMP
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f literals\n", "bumped:",
	    s.bumped, relative (s.bumped, s.conflicts));
#endif
#ifndef NCHRONO
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f per learned\n",
	    "chronological backtracking:", s.chrono,
	    percent (s.chrono, s.learned));
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f per jump\n",
	    "reused level:", s.chronosaved, relative (s.chronosaved,
						      s.chrono));
#endif
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f MB\n", "collected:",
	  s.collected, s.collected / (double) (1u << 20));
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f per second\n", "conflicts:",
	  s.conflicts, relative (s.conflicts, seconds));
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f per conflict\n", "decisions:",
	  s.decisions, relative (s.decisions, s.conflicts));
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f literals\n", "deduced:",
	    s.deduced, relative (s.deduced, s.conflicts));
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  added\n", "deleted:",
	    s.deleted, percent (s.deleted, s.added));
#ifndef NELIMINATION
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  variables\n", "eliminated:",
	  s.eliminated, percent (s.eliminated, s.variables));
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "eliminations:",
	    s.eliminations, relative (s.conflicts, s.eliminations));
#endif
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  variables\n", "fixed:",
	  s.fixed, percent (s.fixed, s.variables));
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f literals\n", "learned:",
	  s.learned, relative (s.learned, s.conflicts));
#ifndef NVSIDS
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  bumped\n", "incremented:",
	    s.incremented, percent (s.incremented, s.bumped));
#endif
#ifndef NMINIMIZE
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  deduced\n", "minimized:",
	    s.minimized, percent (s.minimized, s.deduced));
#endif
#ifndef NVMTF
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  bumped\n", "moved:",
	    s.moved, percent (s.moved, s.bumped));
#endif
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f per second\n", "propagations:",
	  s.propagations, relative (s.propagations, seconds));
#ifndef NBUMPREASONS
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  bumped\n", "reasons:",
	    s.reasons, percent (s.reasons, s.bumped));
#endif
#ifndef NREDUCE
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f per reduction\n", "reduced:",
	  s.reduced, relative (s.reduced, s.reductions));
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "reductions:",
	    s.reductions, relative (s.conflicts, s.reductions));
#endif
#ifndef NREPHASE
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "rephased:",
	  s.rephased, relative (s.conflicts, s.rephased));
#endif
#ifndef NVSIDS
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "rescored:",
	  s.rescored, relative (s.conflicts, s.rescored));
#endif
#ifndef NVMTF
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "restamped:",
	  s.restamped, relative (s.conflicts, s.restamped));
#endif
#ifndef NELIMINATION
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f per variable\n", "resolutions:",
	  s.resolutions, relative (s.resolutions, s.variables));
#endif
#ifndef NRESTART
  printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "restarts:",
	  s.restarts, relative (s.conflicts, s.restarts));
#endif
#ifndef NREUSE
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  restarts\n", "reused:",
	    s.reused, percent (s.reused, s.restarts));
#endif
#ifndef NSHRINK
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  deduced\n", "shrunken:",
	    s.shrunken, percent (s.shrunken, s.deduced));
#endif
#ifndef NSUBSUMPTION
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  added\n", "strengthened:",
	  s.strengthened, percent (s.strengthened, s.added));
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f %%  added\n", "subsumed:",
	  s.subsumed, percent (s.subsumed, s.added));
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "subsumptions:",
	    s.subsumptions, relative (s.conflicts, s.subsumptions));
#endif
#ifndef NSWITCH
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "switched:",
	    s.switched, relative (s.conflicts, s.switched));
#endif
#ifndef NTARGET
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f interval\n", "targets:",
	    s.targets, relative (s.conflicts, s.targets));
#endif
#ifndef NVIVIFICATION
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f per round\n",
	  "vivified:", s.vivified, relative (s.vivified, s.vivifications));
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f per round\n",
	  "     propagations:", s.vivify_propagations,
	  relative (s.vivify_propagations, s.vivifications));
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f per propagation\n",
	  "     ticks:", s.probing_ticks,
	  relative (s.probing_ticks, s.vivify_propagations));
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f per round\n",
	  "     subsume:", s.vivify_subsume,
	  relative (s.vivify_subsume, s.vivifications));
  printf (F1 " %" L2 PRIu64 " %" P3 ".0f per round\n",
	  "     strengthen:", s.vivify_strengthened,
	  relative (s.vivify_strengthened, s.vivifications));
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" P3 ".2f per vivification\n",
	    "     reused:", s.vivify_reused,
	    relative (s.vivify_reused, s.vivified));
#endif
  if (verbose)
    printf (F1 " %" L2 PRIu64 " %" L3 ".2f per propagation\n", "ticks:",
	    s.ticks, relative (s.ticks, s.propagations));
}

static void
print_resource_usage (struct satch *solver, double seconds)
{
  internal_section (solver, "resources");
  const uint64_t memory = maximum_resident_set_size ();
  printf ("c %-24s %17" PRIu64 " bytes %11.2f MB\n",
	  "memory:", memory, memory / (double) (1 << 20));
  printf ("c %-24s %17s %17.2f seconds\n", "time:", "", seconds);
}

