/*------------------------------------------------------------------------*/
#ifndef NVIRTUAL

// This section handles virtual binary clauses which only reside in watch
// lists but are not actually allocated. This feature (disabled without
// defining 'NVIRTUAL') can save up to a factor of four in memory usage.

static inline void
watch_binary (struct satch *solver,
	      bool redundant, unsigned lit, unsigned blocking)
{
  union watch watch;
  watch.header.binary = true;
  watch.header.redundant = redundant;
  watch.header.blocking = blocking;
  PUSH (solver->watches[lit], watch);
  LOGBIN (redundant, lit, blocking,
	  "watching %s blocking %s in", LOGLIT (lit), LOGLIT (blocking));
}

static void
add_new_binary_and_watch_it (struct satch *solver, bool redundant)
{
  assert (SIZE_STACK (solver->clause) == 2);
  const unsigned lit = ACCESS (solver->clause, 0);
  const unsigned other = ACCESS (solver->clause, 1);
  watch_binary (solver, redundant, lit, other);
  watch_binary (solver, redundant, other, lit);
  if (redundant)
    INC (redundant);
  else
    INC (irredundant);
}

#if !defined(NREDUCE) || !defined(NDEBUG) || !defined(NELIMINATION)

// In contrast to large clauses deleting virtual binary clauses does not
// deallocate any memory but statistics have to be adapted.  We also need to
// trigger adding deletion lines to proofs and the checker if enabled.  See
// the corresponding discussion before 'delete_clause' above too.  Last but
// not least we have to update counts of literals and 'eliminate' flags.

static void
really_delete_binary (struct satch *solver,
		      bool redundant, unsigned lit, unsigned other)
{
  LOGBIN (redundant, lit, other, "delete");
  trace_and_check_binary_deletion (solver, lit, other);
#ifndef NELIMINATION
  if (!redundant)
    {
      mark_eliminate_literal (solver, lit);
      mark_eliminate_literal (solver, other);
    }
#endif
  if (redundant)
    DEC (redundant);
  else
    DEC (irredundant);
}

static void
delete_binary (struct satch *solver,
	       bool redundant, unsigned lit, unsigned other)
{
  // We watch 'lit' in the watch list of 'other' and vice versa. Thus when
  // we delete these virtual binary clauses (residing only in watch lists)
  // we do not know which of the two cases we encounter first but both
  // occurrences should trigger 'delete_binary'.  Thus we delete the virtual
  // binary clause only once when 'lit' is smaller than 'other'.

  if (lit < other)
    really_delete_binary (solver, redundant, lit, other);
}

#endif

#ifndef NDEBUG

// Short-hand only used in 'internal_release' in debugging mode.

static void
delete_header (struct satch *solver, unsigned lit, struct header header)
{
  const bool redundant = header.redundant;
  const unsigned blocking = header.blocking;
  delete_binary (solver, redundant, lit, blocking);
}

#endif

#endif // of '#ifndef NVIRTUAL'

/*------------------------------------------------------------------------*/

static void
mark_garbage (struct satch *solver, struct clause *c, const char *msg)
{
#ifndef NVIRTUAL
  assert (!is_tagged_clause (c));
  assert (!is_temporary_binary (solver, c));
#endif
  assert (!c->garbage);
  LOGCLS (c, "%s thus marked garbage", msg);
  c->garbage = true;
  trace_and_check_deletion (solver, c->size, c->literals);
  if (c->redundant)
    DEC (redundant);
  else
    DEC (irredundant);
#ifndef NELIMINATION
  if (!c->redundant)
    {
      mark_eliminate_clause (solver, c);
    }
#endif
#ifndef LOGGING
  (void) msg;			// Prevent unused 'msg' warning.
#endif
}

/*------------------------------------------------------------------------*/

#if !defined(NELIMINATION) || defined(NWATCHES)

// Connect literal in irredundant clause.

static void
connect_literal (struct satch *solver, unsigned lit, struct clause *c)
{
#ifndef NWATCHES
  assert (solver->dense);
#endif
#ifdef LOGGING
#ifndef NVIRTUAL
  if (is_tagged_clause (c))
    LOGTAGGED (lit, c, "connecting %s to", LOGLIT (lit));
  else
#endif
    LOGCLS (c, "connecting %s to", LOGLIT (lit));
#endif
#if !defined(NDEBUG) && !defined(NVIRTUAL)
  if (!is_tagged_clause (c))
    assert (!c->garbage);
#endif
  const union watch watch = {.clause = c };
  PUSH (solver->watches[lit], watch);
}

static void
connect_clause (struct satch *solver, struct clause *c)
{
  for (all_literals_in_clause (lit, c))
    connect_literal (solver, lit, c);
}

/*------------------------------------------------------------------------*/

#if (!defined(NSUBSUMPTION) && !defined(NVIRTUAL)) || \
    (!defined(NELIMINATION) && !defined(NVIRTUAL)) || \
    !defined(NSTRENGTHENING) || \
    ((!defined(NVIVIFICATION) || !defined(NREDUCE) || !defined(NELIMINATION)) && defined(NWATCHES))

static void
disconnect_literal (struct satch *solver, unsigned lit, struct clause *c)
{
#ifndef NWATCHES
  assert (solver->dense);
#endif
#ifdef LOGGING
#ifndef NVIRTUAL
  if (is_tagged_clause (c))
    LOGTAGGED (lit, c, "disconnecting %s from", LOGLIT (lit));
  else
#endif
    LOGCLS (c, "disconnecting %s from", LOGLIT (lit));
#endif
  struct watches *watches = solver->watches + lit;
  const union watch *const end = watches->end;
  union watch *q = watches->begin;
  while (assert (q != end), q->clause != c)
    q++;
  while (++q != end)
    q[-1] = *q;
  watches->end--;
  if (EMPTY_STACK (*watches))
    RELEASE_STACK (*watches);
}

#endif

#endif

/*------------------------------------------------------------------------*/

#ifdef NWATCHES

static void
count_clause (struct satch *solver, struct clause *c)
{
  unsigned sum = 0, count = 0;

  const signed char * const values = solver->values;
#ifndef NCHRONO
  const unsigned propagated = solver->trail.propagate - solver->trail.begin;
#endif
  for (all_literals_in_clause (lit, c))
    {
	signed char tmp = values[lit];
#ifndef NCHRONO
	if (tmp < 0 && solver->position[INDEX (lit)] < propagated)
	  continue;
#else
	if (tmp < 0)
	  continue;
#endif
	count++;
	sum += lit;
    }

  c->sum = sum;
  c->count = count;
  LOGCLS (c, "count set to %u in", count);
}

#endif

/*------------------------------------------------------------------------*/
static inline unsigned
assignement_level (struct satch *solver, unsigned lit, struct clause *reason)
{
  if (!reason
#ifndef NVIVIFICATION
      || solver->vivifying
#endif
      )
    return solver->level;

#ifdef NCHRONO
  (void) reason;
  (void) lit;
  return solver->level;
#else
  struct clause *fullreason;
#ifndef NBLOCK
  if (is_tagged_clause (reason))
    {
      const unsigned other = tagged_clause_to_literal (reason);
      assert (solver->values[other]);
      LOG ("found assignment level %d", solver->levels[INDEX (other)]);
      return solver->levels[INDEX (other)];
    }
  else
#endif
    fullreason = reason;
  unsigned level = 0;
  for (all_literals_in_clause (other, fullreason))
    {
      if (other == lit)
	continue;
      assert (solver->values[other]);
      const unsigned tmp = solver->levels[INDEX (other)];
      if (tmp > level)
	level = tmp;
    }
  LOG ("found assignment level %d", level);
  return level;
#endif
}

// Assigning the literal 'lit' with the reason. Two special cases:
//
//   1. for decisions, the reason is empty but the solver->level > 0
//   2. for units, either known_unit is true or solver->level == 0
//
// The 'known_unit' parameter is not necessary without chronological backtracking.
static void
assign (struct satch *solver, unsigned lit, struct clause *reason,
	bool known_unit)
{
#ifdef LOGGING
#ifndef NBLOCK
  if (is_tagged_clause (reason))
    LOGTAGGED (lit, reason, "assign %s reason", LOGLIT (lit));
  else
#endif
  if (reason)
    LOGCLS (reason, "assign %s reason", LOGLIT (lit));
  else if (!solver->level || known_unit)
    LOG ("assign %s through unit clause %s", LOGLIT (lit), LOGLIT (lit));
  else
    LOG ("assign %s decision", LOGLIT (lit));
#endif

  // Garbage clauses can not be reasons.

#if !defined(NDEBUG) && !defined(NCDCL)
#ifndef NBLOCK
  if (!is_tagged_clause (reason))
#endif
    if (reason)
      assert (!reason->garbage);
#endif

  const unsigned idx = INDEX (lit);
  const unsigned level =
    known_unit ? 0 : assignement_level (solver, lit, reason);
  if (!known_unit && !level)
    {
      LOG ("delayed unit");
      reason = 0;
    }
  known_unit = known_unit || !level;
  if (!solver->level || known_unit)
    {
      LOG ("new fixed %s", LOGLIT (lit));
      solver->statistics.fixed++;	// Root-level fixed literal (unit).

      assert (solver->statistics.remaining);
      solver->statistics.remaining--;	// One less active variable.

      struct flags *f = solver->flags + idx;
      assert (f->active);
      f->active = false;
      assert (!f->fixed);
      f->fixed = true;

      trace_and_check_unit_addition (solver, lit);
      if (reason
#ifdef NCDCL
	  && reason != DUMMY_REASON
#endif
	)
	{
#ifndef NBLOCK
	  if (!is_tagged_clause (reason))
#endif
	    mark_garbage (solver, reason, "root-level forcing");
	  reason = 0;
	}
    }

  const unsigned not_lit = NOT (lit);
  assert (!solver->values[lit]);
  assert (!solver->values[not_lit]);

  // Set value of 'lit' and 'not-lit' independently in order to turn the
  // code for accessing the value of a literal into a simple array look-up
  // as well. This makes it simpler and branch-less too.

  solver->values[lit] = 1;
  solver->values[not_lit] = -1;

#ifndef NSAVE

  // Saved value is used as decision phase if 'idx' is picked as decision.
#ifndef NVIVIFICATION
  if (!solver->vivifying)
#endif
    solver->saved[idx] = INT_SIGN (lit);
#endif
  solver->reasons[idx] = reason;	// Remember reason clause.
  solver->levels[idx] = level;	// Remember decision level.

#ifndef NCONTROL
  solver->position[idx] = SIZE_STACK (solver->trail);
#endif

  // Add literal to the partial assignment in the pre-allocated 'trail'.

  assert (solver->trail.end < solver->trail.begin + VARIABLES);
  *solver->trail.end++ = lit;

#ifndef NCONTROL
  if (reason == 0 && solver->level && !known_unit)
    {
      LOG ("pushing trail position %zd at height %zd",
	   SIZE_STACK (solver->trail), SIZE_STACK (solver->control));
      struct level level = {.trail = solver->trail.end - 1,
	.lvl = solver->level,
	.seen = {.earliest = UINT32_MAX,.count = 0}
      };
      PUSH (solver->control, level);
    }
#endif
  // Used for fast termination check on 'satisfiable' instances.

  assert (solver->unassigned);
  solver->unassigned--;

#ifndef NCONTROL
  assert (solver->level == SIZE_STACK (solver->control));
#endif
}

/*------------------------------------------------------------------------*/

// Activating variables means adding them to the solver.

// It is also helpful to activate variables in the order they appear in the
// input by putting them on each of the two 'put' stacks, which allows to
// delay initialization of the decision queue / heap and only when the queue
// or the heap is queried through 'get_queue' resp. 'get_scores' it is
// filled in the order in which the variables occur in the formula.

static void
activate_literals (struct satch *solver)
{
  struct flags *flags = solver->flags;
  for (all_elements_on_stack (unsigned, lit, solver->clause))
    {
      const unsigned idx = INDEX (lit);
      struct flags *f = flags + idx;
      if (f->active)
	continue;
      f->active = true;
#ifndef NSUBSUMPTION
      f->subsume = 1;
      INC (marked_subsume);
#endif
#ifndef NELIMINATION
      f->eliminate = true;
      INC (marked_eliminate);
#endif
      LOG ("activated %s", LOGVAR (idx));
#ifndef NLAZYACTIVATION
#ifndef NFOCUSED
      PUSH (solver->put[0], idx);
#endif
#ifndef NSTABLE
      PUSH (solver->put[1], idx);
#endif
#endif
      solver->statistics.remaining++;
      solver->statistics.variables++;
      solver->unassigned++;
    }
}

/*------------------------------------------------------------------------*/
#ifndef NQUEUE
/*------------------------------------------------------------------------*/

// Functions to implement a doubly-linked variable decision queue.

#ifndef NBUMP

// We use 32-bit enqueue time stamps which overflow rather frequently after
// roughly 4 billion enqueue operations.  In this case we just go over all
// variable links in order of the decision queue and assign fresh stamps.

// Even for many variables (the maximum variable index is '(1u<<31) - 2') we
// still need a billion enqueue operations before this triggers and thus the
// accumulated complexity for this operation can be ignored.

static void
restamp_queue (struct satch *solver, struct queue *queue)
{
  const uint64_t restamped = INC (restamped);
  message (solver, 2, "restamp", restamped,
	   "restamping indices in decision queue");
  struct link *links = queue->links, *link;
  unsigned stamp = 0;
  for (unsigned idx = queue->first; idx != INVALID; idx = link->next)
    {
      link = links + idx;
      assert (stamp < UINT_MAX);
      link->stamp = ++stamp;
    }
  queue->search = queue->last;
  queue->stamp = stamp;
}

#endif

// Simple doubly linked list enqueue operation at the end of the queue with
// time stamping, where the time is the 'enqueue time'.  The 'search' index
// of the queue is also updated if this variable is unassigned.

static void
enqueue (struct satch *solver, struct queue *queue, unsigned idx)
{
  LOG ("enqueue %u", idx);
  struct link *const links = queue->links;
  struct link *const link = links + idx;
  const unsigned last = queue->last;
  if (last == INVALID)
    {
      assert (queue->first == INVALID);
      queue->first = idx;
    }
  else
    {
      struct link *const prev = links + last;
      assert (prev->next == INVALID);
      prev->next = idx;
    }
  link->prev = last;
  queue->last = idx;
  link->next = INVALID;

  // Now comes the 'stamping' trick from our SAT'2015 paper which makes sure
  // that time stamps respect queue order and can thus be used to compare in
  // constant time whether an element is to the left or right of the cached
  // search index, which during searching for unassigned decision variables
  // is set to the last decision variable index first and then updated in
  // case a variable right to the cached search index becomes unassigned
  // during backtracking.  This technique makes sure that right to the
  // search index all variables are assigned in the decision queue.  See
  // also the code involving stamps in 'backtrack' and in 'decide'.

  link->stamp = ++queue->stamp;
#ifdef NBUMP
  assert (link->stamp);
#else
  if (link->stamp)		// Check for overflow.
#endif
    {
      LOG ("enqueued %s stamped %u", LOGVAR (idx), link->stamp);
      const unsigned lit = LITERAL (idx);
      if (!solver->values[lit])
	queue->search = idx;
    }
#ifndef NBUMP
  else
    restamp_queue (solver, queue);
#endif
}

#ifndef NVMTF

// Simple doubly linked list dequeue operation (no stamping involved).

static void
dequeue (struct satch *solver, struct queue *queue, unsigned idx)
{
  LOG ("dequeue %u", idx);
  struct link *const links = queue->links;
  struct link *const link = links + idx;
  const unsigned prev_idx = link->prev;
  const unsigned next_idx = link->next;
  if (prev_idx == INVALID)
    {
      assert (queue->first == idx);
      queue->first = next_idx;
    }
  else
    {
      struct link *const prev = links + prev_idx;
      assert (prev->next == idx);
      prev->next = next_idx;
    }
  if (next_idx == INVALID)
    {
      assert (queue->last == idx);
      queue->last = prev_idx;
    }
  else
    {
      struct link *next = links + next_idx;
      assert (next->prev == idx);
      next->prev = prev_idx;
    }
}

#endif

/*------------------------------------------------------------------------*/

// The solver might have actually two queues (by default only one in focused
// mode though).  This could in principle be figured out at compile time but
// leads to extremely complex preprocessor macro checking code.  Instead we
// initialize the queue lazily on-demand if 'size' is not big enough.

static void
resize_queue (struct queue *queue, size_t new_capacity)
{
  RESIZE_UNINITIALIZED (queue->links);
}

static void
init_queue (struct satch *solver, struct queue *queue)
{
  if (!queue->size)
    queue->first = queue->last = queue->search = INVALID;
  if (!queue->links)
    resize_queue (queue, solver->capacity);
}

#ifndef NLAZYACTIVATION

// Put variables on the decision queue in the order in which the variables
// are activated (found in the input). Since the last activated variables is
// enqueued last, reverse activation order gives initial decision order.

static void
activate_queue (struct satch *solver, struct queue *queue,
		struct unsigned_stack *activate)
{
  init_queue (solver, queue);
  const unsigned stable = solver->stable;
  LOG ("activating %zu variables on queue[%u]", SIZE_STACK (*activate),
       stable);
  for (all_elements_on_stack (unsigned, idx, *activate))
    {
      INC (activated[stable]);
      enqueue (solver, queue, idx);
    }
  RELEASE_STACK (*activate);
  queue->size = solver->size;
}

#else

// Otherwise put variables on the decision queue in index order.  Since the
// variable with the largest index is enqueued last, reverse index order
// gives the initial decision order.

static void
fill_queue (struct satch *solver, struct queue *queue)
{
  init_queue (solver, queue);
  const unsigned stable = solver->stable;
  LOG ("filling queue[%u] with %zu variables",
       stable, (size_t) (solver->size - queue->size));
  while (queue->size < solver->size)
    {
      INC (filled[stable]);
      enqueue (solver, queue, queue->size++);
    }
}

#endif

static struct queue *
get_queue (struct satch *solver)
{
  const unsigned stable = solver->stable;
  struct queue *queue = &solver->queue[stable];
#ifndef NLAZYACTIVATION
  struct unsigned_stack *activate = &solver->put[stable];
  if (!EMPTY_STACK (*activate))
    activate_queue (solver, queue, activate);
#else
  if (queue->size < solver->size)
    fill_queue (solver, queue);
#endif
  assert (queue->size == solver->size);
  return queue;
}

#ifndef NVMTF

static void
move_variable_to_front (struct satch *solver, unsigned idx)
{
  INC (moved);
  LOG ("moving %s to front of decision queue", LOGVAR (idx));
  struct queue *queue = get_queue (solver);
  dequeue (solver, queue, idx);
  enqueue (solver, queue, idx);
}

#endif

static void
release_queue (struct queue *queue)
{
  free (queue->links);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

// The solver can keep a 'capacity' of allocated variables larger than the
// number 'size' of added variables.  This capacity increases exponentially
// and avoids costly resizing operations of data structures during API
// usage. In stand-alone solver usage the number of variables is fixed and
// thus can be pre-allocated by 'satch_reserve', which avoids any resizing.
// This strategy can of course also be followed through the API if the user
// has a reasonable bound on the number of needed variables.

// This whole section of the code can be simplified substantially if we
// could assume a fixed number of variables, which unfortunately is not
// possible for incremental SAT solving.  We went through the effort to work
// out this resizing logic even though the solver is not incremental yet, as
// currently the API does not allow yet to add further clauses after the
// first call to 'satch_solve' (checked by 'REQUIRE_NON_INCREMENTAL').

// There are no global data structures. Thus multiple solvers can exist at
// the same time in the same process and clauses can be added incrementally
// without forcing the user to define a maximum variable up-front.

/*------------------------------------------------------------------------*/

// In principle we could use an unsigned stack for the trail but we can also
// just pre-allocate it, since it will never contain more literals than the
// number of variables.  In 'C' this allocation will not necessarily occupy
// real memory (in terms of resident set size) even for large instances,
// since for instance Linux would map those allocated pages to real pages
// lazily on-demand.  The pre-allocated trail makes the related code in
// 'assign' and 'boolean_constraint_propagation' more efficient.

static void
resize_trail (struct trail *trail, size_t new_capacity)
{
  assert (new_capacity);
  const size_t size = SIZE_STACK (*trail);
  const size_t bytes = new_capacity * sizeof (unsigned);
  const unsigned propagate = trail->propagate - trail->begin;
  trail->begin = realloc (trail->begin, bytes);
  if (!trail->begin)
    out_of_memory (bytes);
  trail->end = trail->begin + size;
  trail->propagate = trail->begin + propagate;
}

// Here we increase the capacity, i.e., the number of allocated data in
// terms of allocated variables, while 'increase_size' might just activate
// this data to be used if the number of variables increases (the 'size' of
// the solver) but otherwise stays below the allocated capacity.

// Note that, this use of 'size' and 'capacity' follows the same terminology
// as for 'std::vector' in the C++ standard template library.

static void
increase_capacity (struct satch *solver, unsigned new_capacity)
{
  const unsigned old_capacity = solver->capacity;
  LOG ("increasing capacity from %u to %u", old_capacity, new_capacity);
  assert (old_capacity < new_capacity);
  assert (new_capacity <= 1u << 31);
  RESIZE_ZERO_INITIALIZED (2, solver->watches, 0);
  RESIZE_ZERO_INITIALIZED (1, solver->reasons, 0);
  RESIZE_ZERO_INITIALIZED (1, solver->levels, 0);
  RESIZE_ZERO_INITIALIZED (2, solver->values, 0);
#ifndef NSAVE
  RESIZE_ZERO_INITIALIZED (1, solver->saved, 0);
#endif
#ifndef NTARGET
  RESIZE_ZERO_INITIALIZED (1, solver->targets, 0);
#endif
#ifndef NBEST
  RESIZE_ZERO_INITIALIZED (1, solver->bests, 0);
#endif
  RESIZE_ZERO_INITIALIZED (1, solver->marks, 0);
  RESIZE_ZERO_INITIALIZED (1, solver->flags, 0);
  RESIZE_ZERO_INITIALIZED (1, solver->frames, 1);
#ifndef NCONTROL
  RESIZE_UNINITIALIZED (solver->position);
#endif
  resize_trail (&solver->trail, new_capacity);

#ifndef NQUEUE
#ifndef NQUEUE0
  if (solver->queue[0].size)
    resize_queue (&solver->queue[0], new_capacity);
#else
  assert (!solver->queue[0].links);
#endif
#ifndef NQUEUE1
  if (solver->queue[1].size)
    resize_queue (&solver->queue[1], new_capacity);
#else
  assert (!solver->queue[1].links);
#endif
#endif

#ifndef NHEAP
#ifndef NHEAP0
  if (solver->scores[0].size)
    resize_heap (&solver->scores[0], old_capacity, new_capacity);
#else
  assert (!solver->scores[0].begin);
#endif
#ifndef NHEAP1
  if (solver->scores[1].size)
    resize_heap (&solver->scores[1], old_capacity, new_capacity);
#else
  assert (!solver->scores[1].begin);
#endif
#endif
#ifndef NVIVIFICATION
  RESIZE_ZERO_INITIALIZED (1, solver->vivify_marks, 0);
#endif
  solver->capacity = new_capacity;
}

// This function activates all variables with index 'old_size' until
// 'new_size-1'.   After calling this function there are 'new_size' active
// variables (except for already root-level assigned variables).

static void
increase_size (struct satch *solver, unsigned new_size)
{
#if defined(LOGGING)
  const unsigned old_size = solver->size;
  assert (solver->size < new_size);
#endif
  const unsigned old_capacity = solver->capacity;
  assert (new_size <= 1u << 31);
  if (new_size > old_capacity)
    {
      unsigned new_capacity;
      if (new_size > 1u << 30)
	new_capacity = 1u << 31;	// Maximum capacity reached.
      else
	{
	  // Otherwise pick as 'new_capacity' the smallest power of two
	  // larger than 'new_size'.  This ensures a geometric increase.

	  assert (old_capacity <= 1u << 30);
	  new_capacity = 1;

	  while (new_size > new_capacity)
	    {
	      assert (new_capacity <= 1u << 30);
	      new_capacity *= 2;
	    }
	}
      increase_capacity (solver, new_capacity);
    }
  assert (new_size <= solver->capacity);
  LOG ("increase solver size from %u to %u", old_size, new_size);
  solver->size = new_size;
}

/*------------------------------------------------------------------------*/

// Signed marking of a literal in essence marks variables as negative or
// positive and is used in checking clauses or resolvents to contain both
// a positive and a negative occurrence of a literal.

static void
mark_literal (signed char *marks, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  assert (!marks[idx]);
  marks[idx] = INT_SIGN (lit);
}

static signed char
marked_literal (const signed char *marks, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  signed char res = marks[idx];
  if (SIGN_BIT (lit))
    res = -res;
  return res;
}

static void
unmark_literal (signed char *marks, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  marks[idx] = 0;
}

/*------------------------------------------------------------------------*/

// Check whether the imported clause contains a literal and its negation or
// is satisfied by a root-level assigned literal.  If neither is the case
// this function removes duplicated and root-level falsified literals.

static bool
imported_clause_trivial_or_satisfied (struct satch *solver)
{
  assert (!solver->level);
  const unsigned *const end_clause = solver->clause.end;
  unsigned *const begin_clause = solver->clause.begin;
  unsigned *q = begin_clause;
  bool trivial = false;
  signed char *const marks = solver->marks;
  const signed char *const values = solver->values;
  for (const unsigned *p = begin_clause; p != end_clause; p++)
    {
      const unsigned lit = *p;
      const signed char value = values[lit];
      if (value < 0)
	{
	  LOG ("skipping falsified literal %s", LOGLIT (lit));
	  continue;
	}
      if (value > 0)
	{
	  LOG ("found satisfied literal %s", LOGLIT (lit));
	  trivial = true;
	  break;
	}
      const signed char prev = marked_literal (marks, lit);
      if (prev > 0)
	{
	  LOG ("skipping duplicated literal %s", LOGLIT (lit));
	  continue;
	}
      if (prev < 0)
	{
	  LOG ("clause contains both literal %s and its negation %s",
	       LOGLIT (NOT (lit)), LOGLIT (lit));
	  trivial = true;
	  break;
	}
      *q++ = lit;
      mark_literal (marks, lit);
    }
  solver->clause.end = q;
  for (const unsigned *p = begin_clause; p != q; p++)
    unmark_literal (marks, *p);
  return trivial;
}

/*------------------------------------------------------------------------*/

// The logic for importing literals follows the description above:

// 'elit' signed external literal (as in API and DIMACS format)
// 'eidx' signed external variable index (in the range '1...INT_MAX')
// 'iidx' unsigned internal variable index (in the range '0...(INT_MAX-1)')
// 'ilit' unsigned internal literal (in the range '0...2*(INT_MAX-1)+1')

static unsigned
import_literal (struct satch *solver, int elit)
{
  assert (elit);
  assert (elit != INT_MIN);	// Otherwise 'abs(elit)' might be undefined.
  const int eidx = abs (elit);
  const unsigned iidx = eidx - 1;
  if (iidx >= solver->size)
    increase_size (solver, iidx + 1);
  unsigned ilit = LITERAL (iidx);
  if (elit < 0)
    ilit = NOT (ilit);
  LOG ("imported external literal %d as internal literal %u", elit, ilit);
  return ilit;
}

/*------------------------------------------------------------------------*/

// Estimate the number of cache lines spanning the given array.

// We could use the numerical vales of the 'begin' and 'end' pointers of the
// array but that would make the code dependent on memory addresses which
// should be avoided.  Therefore we fall back to an estimation, which in
// essence assumes that the start address is cache-line-size aligned.

// Typical size of a cache line is 128 bytes, but even if your processor has
// less or more, this computation is anyhow just a rough estimate and by
// keeping it machine independent we also keep scheduling of for instance
// the focused and stable phases and thus the whole solver execution machine
// independent (does not vary for different cache-line size).

#define log2_bytes_per_cache_line	7
#define bytes_per_cache_line		(1u << log2_bytes_per_cache_line)

static inline size_t
cache_lines (const void *begin, const void *end)
{
  assert (begin <= end);
  const size_t round = bytes_per_cache_line - 1;
  const size_t bytes = (char *) end - (char *) begin;
  const size_t res = (bytes + round) >> log2_bytes_per_cache_line;
  return res;
}

// Short-cut for further usage on stacks.

#define CACHE_LINES_OF_STACK(S) cache_lines ((S)->begin, (S)->end)

/*------------------------------------------------------------------------*/

#ifndef NWATCHES

// ------------------------ //
// Propagation with watches //
// ------------------------ //

// Propagating a literal over the clauses in which it occurs negatively,
// more precisely for which its negation is watched, is the hot-spot of
// CDCL solving.  This is further pronounced by learning many long clauses.

static struct clause *
propagate_literal (struct satch *solver, unsigned lit,
		   struct clause *ignore, uint64_t * ticking)
{
  LOG ("propagating %s", LOGLIT (lit));

  const unsigned not_lit = NOT (lit);
  struct watches *const watches = solver->watches + not_lit;
  signed char *const values = solver->values;

#ifndef NVIVIFICATION
  if (!solver->vivifying)
#endif
    assert (ignore == NULL);

  // We traverse all the watches of the literal 'not_lit' and remove those
  // for which we stop watching the clause (since we found a replacement).
  // The updated watches pointer 'q' follows the traversal pointer 'p'.

  union watch *q = watches->begin;
  const union watch *p = q;

  struct clause *conflict = 0;

  const union watch *const end_watches = watches->end;

  // By counting 'tick's we approximate the number of cache lines read in
  // 'propagation' focusing on accessing memory of watch stacks, and clause
  // memory.  And assignment is also counted as one cache line access
  // ('tick') but we do not take reading assigned values into account,
  // assuming those single byte accesses are shared.

  // Since the size of watches differs with and without 'NVIRTUAL' defined,
  // the size of the accessed memory changes too which in turn changes the
  // global scheduling of focused and stable mode based on ticks.

  // Trying to avoid this kind of non-determinism with respect to using
  // virtual clause or not would require to sort reason literals of binary
  // clauses in order to avoid different traversals during conflict
  // analysis.  It also changes when compiling on a 32-bit machine.

  // Furthermore it is pretty difficult to keep the same behaviour with and
  // without blocking literals (avoiding different watch replacement).

  uint64_t ticks = 1 + cache_lines (q, end_watches);

  while (!conflict && p != end_watches)
    {
#ifndef NBLOCK
      const union watch watch = *q++ = *p++;	// Keep header by default.
      const struct header header = watch.header;
      const unsigned blocking_lit = header.blocking;
      const signed char blocking_value = values[blocking_lit];

      // There is dedicated code for propagating over binary clauses.  With
      // the blocking literal stored in the watcher-stack there is no need
      // to access the actual binary clauses here (even if non-virtual).

      if (header.binary)
	{
	  if (blocking_value < 0)
	    {
	      conflict = binary_clause (solver, 0,
					header.redundant,
					not_lit, blocking_lit);
	      LOGCLS (conflict, "conflicting");
	    }
	  else if (!blocking_value)
	    {
	      assert (!blocking_value);
	      assign (solver, blocking_lit,
		      tag_binary_clause (header.redundant, not_lit), false);
	      ticks++;
	    }
#ifdef NVIRTUAL
	  *q++ = *p++;		// Copy clause too.
#endif
	  continue;
	}
      else
#endif
	// Handle larger non-binary clause in case blocking literals are
	// enabled or both cases (binary and non-binary clauses) if they are.

	{
	  struct clause *clause = (*q++ = *p++).clause;	// Copy clause.
	  if (clause->garbage)
	    LOGCLS (clause, "clause should not be garbage");
	  assert (!clause->garbage);
	  if (clause == ignore) {
	    continue;
    }
#ifndef NBLOCK
	  if (blocking_value > 0)
	    continue;
#endif
	  unsigned *const literals = clause->literals;

	  // At this point we have to access the large clause. This is the
	  // real hot-spot of the solver.  Up-to 80% of the time can be
	  // spent here in the first pointer access without the blocking
	  // literal idea (and specialized binary clause propagation above).

	  // In the source code below with the assertion above disabled the
	  // first pointer access would be accessing the first literal
	  // 'literals[0]' of the clause.  The main purpose of the 'blocking
	  // literal' idea is to reduce the need for this costly pointer
	  // dereference as much as possible.

	  ticks++;		// We mainly count these accesses.

	  // The two watched literals of a clause are stored as the first
	  // two literals but we do not know at which position.  In order to
	  // avoid introducing a 'branch' (if-then-else) we simply use the
	  // trick to compute the XOR of the first two literals and the
	  // watched literal 'not_lit', which gives the other literal.

	  const unsigned other = literals[0] ^ literals[1] ^ not_lit;
	  const signed char other_value = values[other];

	  // Another common situation is that the other watched literal in
	  // that clause is different from the blocking literal, but is
	  // assigned true.  Then we also can stop here after updating the
	  // blocking literal for this watch to this other literal.

	  if (other_value > 0)
	    {
#ifndef NBLOCK
	      q[-2].header.blocking = other;
#endif
	      continue;
	    }

	  // Normalize the position where 'not_lit' sits to position '1'.

	  literals[0] = other;
	  literals[1] = not_lit;

	  const unsigned size = clause->size;
	  const unsigned *const end_literals = literals + size;

	  // Now search for a non-false ('true' or unassigned) replacement
	  // for the watched literal 'not_lit' starting with the third.

	  unsigned replacement = INVALID;
	  signed char replacement_value = -1;
	  const unsigned *end_search = end_literals;
	  unsigned *start_search = literals + 2, *r;
#ifndef NCACHE

	  // Use and remember the old offset were we found a replacement
	  // watch or a satisfied blocking literal and resume next search of
	  // replacement literals in this clause at that position (relative
	  // to 'literals + 2').

	  start_search += clause->search;
#endif
	  for (r = start_search; r != end_search; r++)
	    {
	      replacement = *r;
	      replacement_value = values[replacement];
	      if (replacement_value >= 0)
		break;
	    }
#ifndef NCACHE
	  if (replacement_value < 0)
	    {
	      end_search = start_search;
	      start_search = literals + 2;

	      for (r = start_search; r != end_search; r++)
		{
		  replacement = *r;
		  replacement_value = values[replacement];
		  if (replacement_value >= 0)
		    {
		      clause->search = r - start_search;
		      break;
		    }
		}
	    }
	  else
	    clause->search = r - start_search;
#endif
	  if (replacement_value > 0)	// Replacement literal true.
	    {
#ifndef NBLOCK
	      // Update blocking literal only.

	      q[-2].header.blocking = replacement;
#endif
	    }
	  else if (!replacement_value)	// Replacement literal unassigned.
	    {
	      // First log the untouched clause, then stop watching the
	      // originally watched literal by simply decreasing 'q'.

	      // Depending on whether blocking literals are disabled the
	      // actual decrement is either '2' (if 'NBLOCK' is defined) or
	      // '1' (if 'NBLOCK' is undefined). This difference is hidden
	      // in the definition of 'long_clause_watch_size'.

	      LOGCLS (clause, "unwatching %s in", LOGLIT (not_lit));
	      q -= long_clause_watch_size;

	      // Swap watched literal with its replacement.

	      literals[1] = replacement;
	      *r = not_lit;

#ifndef NBLOCK
	      const bool redundant = clause->redundant;
	      watch_literal (solver, redundant, replacement, other, clause);
#else
	      watch_literal (solver, replacement, clause);
#endif
	      ticks++;
	    }
	  else if (other_value)
	    {
	      // Clause is conflicting, since all literals are false!

	      assert (other_value < 0);
	      LOGCLS (clause, "conflicting");
	      conflict = clause;
	    }
	  else
	    {
	      // All literals are false except 'other' which is unassigned
	      // and thus it is now assigned with this clause as reason.

	      assert (!other_value);
	      assign (solver, other, clause, false);
	      ticks++;
	    }
	}
    }

  *ticking += ticks;

  // After a conflicting clause is found we break out of the propagation but
  // still need to copy the rest of the watches and reset the stack size.

  while (p != end_watches)
    *q++ = *p++;
  watches->end = q;

  return conflict;
}

#else // of '#ifndef NWATCHES'

// ------------------------- //
// Propagation with counters //
// ------------------------- //

// Updating the non-false literal counters of literals in clauses is the
// hot-spot for CDCL with counters (instead of watches).  This effort occurs
// during propagation in this function and then also during backtracking.

struct clause *
propagate_literal (struct satch *solver, unsigned lit, struct clause *ignore, uint64_t * ticking)
{
  LOG ("propagating %s", LOGLIT (lit));

  const unsigned not_lit = NOT (lit);
  struct watches *const watches = solver->watches + not_lit;
  signed char *const values = solver->values;

  // We traverse all clauses containing literal 'not_lit' and decrement the
  // non-false literal counters and update the sum of non-false literals in
  // order to find a conflict as well as detecting new units.

  uint64_t ticks = 1 + cache_lines (watches->begin, watches->end);
  struct clause *conflict = 0;

  for (all_elements_on_stack (union watch, watch, *watches))
    {
      struct clause * const clause = watch.clause;
      assert (clause->count > 0);
      clause->count--;
      clause->sum -= not_lit;
      LOGCLS (clause, "count decreased to %u in", clause->count);
      ticks++;
      if (clause == ignore)
        continue;
      if (conflict)
	continue;
      if (!clause->count)
	{
	  LOGCLS (clause, "conflicting");
	  conflict = clause;
	}
      else if (clause->count == 1)
	{
	  const unsigned unit = clause->sum;
	  const signed char value = values[unit];
	  if (!value)
	    {
	      assign (solver, unit, clause, false);
	      ticks++;
	    }
	  else if (value  < 0)
	    {
	      LOGCLS (clause, "conflicting");
	      conflict = clause;
	    }
	}
    }

  *ticking += ticks;

  return conflict;
}

// Without watches and just counters we have to update the counters of
// propagated literals during backtracking, which we call 'unpropagating'.

static void
unpropagate_literal (struct satch * solver, unsigned lit)
{
  LOG ("unpropagating %s", LOGLIT (lit));

  const unsigned not_lit = NOT (lit);
  struct watches *const watches = solver->watches + not_lit;

  // We traverse all clauses containing literal 'not_lit' and increment the
  // non-false literal counters and adjust the non-false literal sum as well.

  uint64_t ticks = 1 + cache_lines (watches->begin, watches->end);

  for (all_elements_on_stack (union watch, watch, *watches))
    {
      struct clause * const clause = watch.clause;
      if (!(clause->count < clause->size))
	LOGCLS (clause, "wrong counter");
      assert (clause->count < clause->size);
      clause->count++;
      clause->sum += not_lit;
      LOGCLS (clause, "count increased to %u in", clause->count);
      ticks++;
    }

  ADD (ticks, ticks);
}

#endif

/*------------------------------------------------------------------------*/

// Flush unit clauses from trail after root-level propagation.  Otherwise
// the statistics of the saved trail become incorrect and the assumption
// that there are no root-level assigned units on the trail break (for
// instance in 'reuse_trail').

// For chronological backtracking we flush only the units that are at the
// beginning of the trail -- this is critical because multiple propagations
// paths could lead to a unit propagation to not be propagated on level 0.
static void
flush_units (struct satch *solver)
{
  struct trail *trail = &solver->trail;
#ifndef NCHRONO
  assert (trail->propagate >= trail->begin);
  assert (trail->propagate <= trail->end);
  unsigned *new_start = trail->begin;
  while (new_start < trail->end && !solver->levels[INDEX (*new_start)])
    {
      ++new_start;
    }
  const long int delta = new_start - trail->begin;
  trail->propagate -= delta;
  assert (trail->propagate >= trail->begin);
  LOG ("chrono flushing %zu root-level units on trail", delta);
  unsigned *lit = trail->begin;

  while (new_start != trail->end)
    *(lit++) = *(new_start++);

  for (struct level * lvl = solver->control.begin; lvl != solver->control.end;
       ++lvl)
    {
      lvl->trail -= delta;
      assert (lvl->trail >= trail->begin);
    }
  assert (lit <= trail->end);
  trail->end = lit;
  assert (trail->propagate >= trail->begin);
  assert (trail->propagate <= trail->end);
  assert (SIZE_STACK (solver->control) == solver->level);
#else
  assert (!solver->level);
  assert (trail->propagate == trail->end);
  LOG ("flushing %zu root-level units on trail", SIZE_STACK (solver->trail));
  trail->propagate = trail->end = trail->begin;
#endif

}

/*------------------------------------------------------------------------*/

// While 'propagate_literal' propagates the assignment of one literal, the
// process of 'boolean constraint propagation' (BCP) implemented in the next
// function propagates all not yet propagated literals pushed on the trail.

// Note that propagation of a literal might produce new assigned literals
// (beside finding conflicting clauses) and thus the following loop can be
// seen as breadth-first search over the unit implied literals of the
// current assignment.

static struct clause *
boolean_constraint_propagation (struct satch *solver)
{
  LOG ("BCP");
  struct trail *trail = &solver->trail;
  unsigned *propagate = trail->propagate;
  unsigned *p;

  assert (trail->begin <= propagate);
  assert (propagate <= trail->begin + VARIABLES);

  struct clause *conflict = 0;
  uint64_t ticks = 0;

  for (p = propagate; !conflict && p != trail->end; p++)
    conflict = propagate_literal (solver, *p, NULL, &ticks);

  ADD (ticks, ticks);
  solver->trail.propagate = p;
  const unsigned propagated = p - propagate;

  ADD (propagations, propagated);

  if (conflict)
    INC (conflicts);
  else if (!solver->level
#ifndef NCHRONO
	   || solver->iterate
#endif
    )
    flush_units (solver);

  return conflict;
}
