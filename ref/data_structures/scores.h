#ifndef NHEAP

static void
init_scores (struct satch *solver, struct heap *scores)
{
  if (!scores->increment)
    scores->increment = 1.0;
  if (!scores->begin)
    resize_heap (scores, 0, solver->capacity);
}

#ifndef NLAZYACTIVATION

// Put variables on the scores binary heap in the order in which the
// variables are activated (found in the input). Since the first activated
// variable is pushed first, activation order gives initial decision order.

// In contrast to MiniSAT and descendants we initialize last activated
// variables with the largest score '1-1/activated', which in essence
// matches the decision order of the queue.

// In MiniSAT almost the same would happen except for the first decision.
// The first decision in MiniSAT is the first variable pushed on the heap.
// After it is taken out (when searching for the next decision), the last
// variable of the heap is swapped with it and thus the last activated
// variable is taken as next decision.  This continues until the first
// conflict is hit, but in principle MiniSAT code loosely matches our
// initialization of scores and how we initialize decision queue.

static void
activate_scores (struct satch *solver, struct heap *scores,
		 struct unsigned_stack *activate)
{
  init_scores (solver, scores);
  const unsigned stable = solver->stable;
  LOG ("activating %zu variables on scores[%u]", SIZE_STACK (*activate),
       stable);
  unsigned *pos = scores->pos;
  double *score = scores->score;
  for (all_elements_on_stack (unsigned, idx, *activate))
    {
      const uint64_t activated = INC (activated[stable]);
      pos[idx] = INVALID;
      score[idx] = 1 - 1.0 / activated;
      push_heap (solver, scores, idx);
    }
  RELEASE_STACK (*activate);
  scores->size = solver->size;
}

#else

// Put variables on the scores binary heap in index order. Without the
// initial score assignment '1-1/filled' below this would match what MiniSAT
// and descendants would do.  See discussion above too.

static void
fill_scores (struct satch *solver, struct heap *scores)
{
  init_scores (solver, scores);
  const unsigned stable = solver->stable;
  LOG ("filling scores[%u] with %zu variables",
       stable, (size_t) (solver->size - scores->size));
  if (scores->size == solver->size)
    return;
  unsigned *pos = scores->pos;
  double *score = scores->score;
  const size_t delta = solver->size - scores->size;
  memset (pos + scores->size, 0xff, delta * sizeof *pos);
  while (scores->size < solver->size)
    {
      const uint64_t filled = INC (filled[stable]);
      const unsigned idx = scores->size++;
      score[idx] = 1 - 1.0 / filled;
      push_heap (solver, scores, idx);
    }
}

#endif

static struct heap *
get_scores (struct satch *solver)
{
  const unsigned stable = solver->stable;
  struct heap *scores = &solver->scores[stable];
#ifndef NLAZYACTIVATION
  struct unsigned_stack *activate = &solver->put[stable];
  if (!EMPTY_STACK (*activate))
    activate_scores (solver, scores, activate);
#else
  if (scores->size < solver->size)
    fill_scores (solver, scores);
#endif
  assert (scores->size == solver->size);
  return scores;
}

#ifndef NVSIDS

static void
bump_variable_score (struct satch *solver, unsigned idx)
{
  INC (incremented);
  struct heap *scores = get_scores (solver);
  const double old_score = heap_score (scores, idx);
  const double new_score = old_score + scores->increment;
  LOG ("bumping score of %s to %g", LOGVAR (idx), new_score);
  update_heap (solver, scores, idx, new_score);
  if (new_score > MAX_SCORE)
    rescore_scores (solver, scores);
}

static void
bump_score_increment (struct satch *solver)
{
  struct heap *scores = get_scores (solver);
  scores->increment *= scores->factor;
  LOG ("new score increment %g", scores->increment);
}

#endif

#endif

#ifdef DLIS
static bool
update_score_dlis (struct satch *solver, struct clause *cl, unsigned *counts,
		   signed char const *const values)
{
  bool satisfied = false;
  for (all_literals_in_clause (lit, cl))
    {
      if (values[lit] || !solver->flags[INDEX (lit)].active)
	{
	  satisfied = true;
	  break;
	}
    }
  if (satisfied)
    {
      LOGCLS (cl, "clause is satisfied or should be skipped");
      return true;
    }


  const int shift = 12 - cl->size;
  const int64_t score = shift < 1 ? 1 : (1l << shift);

  for (all_literals_in_clause (lit, cl))
    {
      counts[lit] += score;
    }
  return false;
}

// The algorithm should also give values to inactive variables too. However,
// those variables should only be set at the very end, when all other variables
// have been set (and the problem is SAT -- this is required in order to
// reconstruct the model in case of elimination). We chose to not require this
// from the rank function (hence the 'inactive' flag in the last loop).
static unsigned
max_score_dlis (struct satch *solver)
{
  assert (EMPTY_STACK (solver->analyzed));
  signed char *values = solver->values;
  struct flags const *const flags = solver->flags;
  unsigned *counts = calloc (LITERALS, sizeof (unsigned));
  assert (SIZE_STACK (solver->irred_sat_upto) + 1 == solver->level);
  assert (SIZE_STACK (solver->red_sat_upto) + 1 == solver->level);
  int sat_upto =
    EMPTY_STACK (solver->irred_sat_upto) ? 0 : TOP (solver->irred_sat_upto);

  for (int i = solver->irredundant.end - solver->irredundant.begin - 1;
       i >= sat_upto;)
    {
      struct clause *cl = solver->irredundant.begin[i];
      if (cl->garbage)
	{
	  --i;
	  continue;
	}
      LOGCLS (cl, "checking clause for DLIS");
      if (update_score_dlis (solver, cl, counts, values))
	{
	  struct clause *tmp = solver->irredundant.begin[sat_upto];
	  solver->irredundant.begin[sat_upto++] = cl;
	  solver->irredundant.begin[i] = tmp;
	}
      else
	--i;
    }

  PUSH (solver->irred_sat_upto, sat_upto);
  sat_upto =
    EMPTY_STACK (solver->red_sat_upto) ? 0 : TOP (solver->red_sat_upto);

  for (int i = solver->redundant.end - solver->redundant.begin - 1;
       i >= sat_upto;)
    {
      struct clause *cl = solver->redundant.begin[i];
      LOGCLS (cl, "checking clause for DLIS");
      if (cl->garbage)
	{
	  --i;
	  continue;
	}
      if (update_score_dlis (solver, cl, counts, values))
	{
	  struct clause *tmp = solver->redundant.begin[sat_upto];
	  solver->redundant.begin[sat_upto++] = cl;
	  solver->redundant.begin[i] = tmp;
	}
      else
        --i;
    }

  PUSH (solver->red_sat_upto, sat_upto);

  for (all_literals (lit))
    {
      if (values[lit] != 0)
	continue;
      if (!flags[INDEX (lit)].active)
	continue;
#if !defined(NBLOCK) && !defined(NVIRTUAL)
      struct watches *watches = solver->watches + lit;
      const union watch *const end = watches->end;
      for (const union watch * p = watches->begin; p != end; p++)
	{
	  const struct header header = p->header;
	  if (header.binary)
	    {
	      const unsigned blocking_lit = header.blocking;
	      if (values[blocking_lit] != 1)
		update_score_dlis (solver, binary_clause (solver, 0,
							  header.redundant,
							  NOT (lit),
							  blocking_lit),
				   counts, values);
	    }
	  else
              ++p;
	}
#endif
    }

#define rank_analyzed(A) \
      (counts [LITERAL (A)] * counts [NOT (LITERAL(A))])

  unsigned var = INVALID;
  unsigned score = 0;
  bool inactive = true; // inactive has lowest possible rank
  for (all_variables (idx)) {
    if (solver->values[LITERAL (idx)])
      continue;
    if (var == INVALID) {
      var = idx;
      if (solver->flags[idx].active)
        score = rank_analyzed (idx), inactive = false;
      continue;
    }
    if (!solver->flags[idx].active)
      continue;
    if (inactive || score > rank_analyzed (idx)) {
      score = rank_analyzed (idx);
      var = idx;
    }
  }

#ifdef NSAVE
  unsigned lit;
  if (counts[LITERAL (var)] > counts[NOT (LITERAL (var))])
    lit = LITERAL (var);
  else
    lit = NOT (LITERAL (var));
  CLEAR_STACK (solver->analyzed);
  free (counts);
  LOG ("DLIS selecting lit %s", LOGLIT (lit));
  return lit;
#else
  CLEAR_STACK (solver->analyzed);
  free (counts);
  LOG ("DLIS selecting var %s", LOGLIT (LITERAL (var)));
  return var;
#endif
}

/*------------------------------------------------------------------------*/
#endif
