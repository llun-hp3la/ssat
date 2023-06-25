/*------------------------------------------------------------------------*/

// The following macro increases the array given as argument which either
// comes as variable indexed array ('FACTOR=1') or literal indexed array
// ('FACTOR=2'). This reallocation would be more complex to code for signed
// 'int' literals and is one of the reasons we use 'unsigned' literals.

// The last argument is for 'frames' which should be of size 'size + 1'
// since they are accessed through the solver level, which can reach 'size'
// even though probably not in the situation where 'frames' is accessed.
// Nevertheless we accommodate for this potential off-by-one allocation by
// adding 'ADJUST' to the size.

#define RESIZE_UNINITIALIZED(P) \
do { \
  const size_t new_bytes = (size_t) new_capacity * sizeof *(P); \
  (P) = realloc ((P), new_bytes); \
  if (!(P)) \
    out_of_memory (new_bytes); \
} while (0)

#define RESIZE_ZERO_INITIALIZED(FACTOR,P,ADJUST) \
do { \
  const size_t size = sizeof *(P); \
  const size_t old_bytes = \
    old_capacity ? FACTOR * (size_t) (old_capacity + ADJUST) * size : 0; \
  const size_t new_bytes = FACTOR * \
                           (size_t) (new_capacity + ADJUST) * size; \
  void * chunk = calloc (new_bytes, 1); \
  if (!chunk) \
    out_of_memory (new_bytes); \
  if (old_bytes) \
    memcpy (chunk, (P), old_bytes); \
  free ((P)); \
  (P) = chunk; \
} while (0)

/*------------------------------------------------------------------------*/
#ifndef NHEAP
/*------------------------------------------------------------------------*/

// Functions to implement a binary heap with embedded scores and, in
// particular, a score update function used for the priority queue for
// decision variables, i.e., the EVSIDS scheme.

// As with queues this heap might have two instances in the solver but in
// default compilation only one for stable mode is actually used and
// initialized lazily on-demand, i.e., by comparing the solver size with the
// zero initialized 'size'.

#if 0

static void
check_heap (struct heap *heap)
{
#ifndef NDEBUG
  const unsigned size = SIZE_STACK (*heap);
  const unsigned *const begin = heap->begin;
  const unsigned *const pos = heap->pos;
  const double *const score = heap->score;
  for (unsigned i = 0; i < size; i++)
    {
      const unsigned idx = begin[i];
      const unsigned idx_pos = pos[idx];
      assert (idx_pos == i);
      unsigned child_pos = 2 * idx_pos + 1;
      unsigned parent_pos = (child_pos - 1) / 2;
      assert (parent_pos == idx_pos);
      if (child_pos < size)
	{
	  unsigned child = begin[child_pos];
	  assert (score[idx] >= score[child]);
	  if (++child_pos < size)
	    {
	      parent_pos = (child_pos - 1) / 2;
	      assert (parent_pos == idx_pos);
	      child = begin[child_pos];
	      assert (score[idx] >= score[child]);
	    }
	}
    }
#else
  (void) heap;			// Prevent unsigned 'heap' warning.
#endif
}

#else
#define check_heap(...) do { } while (0)
#endif

static void
bubble_up (struct satch *solver, struct heap *heap, unsigned idx)
{
  unsigned *stack = heap->begin;
  unsigned *pos = heap->pos;
  unsigned idx_pos = pos[idx];
  const double *const score = heap->score;
  const double idx_score = score[idx];
  while (idx_pos)
    {
      const unsigned parent_pos = (idx_pos - 1) / 2;
      const unsigned parent = stack[parent_pos];
      const double parent_score = score[parent];
      if (parent_score >= idx_score)
	break;

      LOG ("swap heap[%u] = %u (%g) with heap[%u] = %u (%g)",
	   idx_pos, idx, idx_score, parent_pos, parent, parent_score);

      stack[idx_pos] = parent;
      pos[parent] = idx_pos;
      idx_pos = parent_pos;
    }
  stack[idx_pos] = idx;
  pos[idx] = idx_pos;
  LOG ("settled to heap[%u] = %u (%g)", idx_pos, idx, idx_score);
  check_heap (heap);
}

static void
bubble_down (struct satch *solver, struct heap *heap, unsigned idx)
{
  const double *score = heap->score;
  unsigned *begin = heap->begin;
  unsigned *pos = heap->pos;

  const unsigned size = SIZE_STACK (*heap);

  const double idx_score = score[idx];
  unsigned idx_pos = pos[idx];

  for (;;)
    {
      unsigned child_pos = 2 * idx_pos + 1;
      if (child_pos >= size)
	break;

      unsigned child = begin[child_pos];
      double child_score = score[child];

      const unsigned sibling_pos = child_pos + 1;
      if (sibling_pos < size)
	{
	  const unsigned sibling = begin[sibling_pos];
	  const double sibling_score = score[sibling];
	  if (sibling_score > child_score)
	    {
	      child = sibling;
	      child_pos = sibling_pos;
	      child_score = sibling_score;
	    }
	}

      if (child_score <= idx_score)
	break;

      assert (idx_pos < child_pos);
      LOG ("swap heap[%u] = %u (%g) with heap[%u] = %u (%g)",
	   idx_pos, idx, idx_score, child_pos, child, child_score);

      begin[idx_pos] = child;
      pos[child] = idx_pos;
      idx_pos = child_pos;
    }
  begin[idx_pos] = idx;
  pos[idx] = idx_pos;
  LOG ("settled to heap[%u] = %u (%g)", idx_pos, idx, idx_score);
  check_heap (heap);
}

static void
push_heap (struct satch *solver, struct heap *heap, unsigned idx)
{
  const unsigned size = SIZE_STACK (*heap);
  assert (size < solver->size);
  unsigned *pos = heap->pos;
  assert (pos[idx] == INVALID);
  pos[idx] = size;
  *heap->end++ = idx;
  LOG ("push heap[%u] = %u (%g)", size, idx, heap->score[idx]);
  bubble_up (solver, heap, idx);
}

static unsigned
max_heap (struct heap *heap)
{
  return ACCESS (*heap, 0);
}

static unsigned
pop_heap (struct satch *solver, struct heap *heap)
{
  check_heap (heap);
  const unsigned res = max_heap (heap);
  LOG ("pop heap[0] = %u (%g)", res, heap->score[res]);
  unsigned *pos = heap->pos;
  assert (!pos[res]);
  pos[res] = INVALID;
  const unsigned last = POP (*heap);
  if (last == res)
    return res;
  pos[last] = 0;
  heap->begin[0] = last;
  bubble_down (solver, heap, last);
  return res;
}

#ifndef NVSIDS

static void
update_heap (struct satch *solver, struct heap *heap,
	     unsigned idx, double new_score)
{
  check_heap (heap);
  double *score = heap->score;
  const double old_score = score[idx];
  if (old_score < new_score)
    {
      score[idx] = new_score;
      if (heap->pos[idx] != INVALID)
	bubble_up (solver, heap, idx);
    }
  else if (old_score > new_score)
    {
      if (heap->pos[idx] != INVALID)
	bubble_down (solver, heap, idx);
    }
}

static double
heap_score (struct heap *heap, unsigned idx)
{
  return heap->score[idx];
}

static void
rescore_scores (struct satch *solver, struct heap *scores)
{
  const uint64_t rescored = INC (rescored);
  const unsigned size = solver->size;
  double *score = scores->score;
  assert (size);
  double max_score = score[0];
  for (unsigned idx = 1; idx < size; idx++)
    {
      const double tmp_score = score[idx];
      if (tmp_score > max_score)
	max_score = tmp_score;
    }
  assert (max_score);
  message (solver, 2, "rescore", rescored,
	   "rescoring heap with maximum score %g", max_score);
  for (unsigned idx = 0; idx < size; idx++)
    score[idx] /= max_score;
  scores->increment /= max_score;
  message (solver, 3, "rescore", rescored,
	   "new score increment %g", scores->increment);
}

#endif

/*------------------------------------------------------------------------*/

static void
resize_heap (struct heap *heap, size_t old_capacity, size_t new_capacity)
{
  const size_t size = SIZE_STACK (*heap);
  RESIZE_UNINITIALIZED (heap->begin);
  heap->end = heap->begin + size;
  RESIZE_UNINITIALIZED (heap->pos);
  RESIZE_ZERO_INITIALIZED (1, heap->score, 0);
}

static void
release_heap (struct heap *heap)
{
  free (heap->begin);
  free (heap->pos);
  free (heap->score);
  memset (heap, 0, sizeof *heap);
}

#endif