/*------------------------------------------------------------------------*/

// Watches are made of a watch header and a clause unless blocking literals
// are disabled ('NBLOCK' defined).  If blocking literals are enabled
// ('NBLOCK' undefined) the blocking literal and thus the header is
// enough to watch a binary clause and the clause pointer can be omitted.

// Actually, binary clauses can become completely 'virtual' and do not have
// to be stored at all outside of watch lists.  Thus in the default compact
// compilation mode ('NVIRTUAL' undefined) we split watches into the two
// parts 'binary' and 'clause' and then use a 'union' type for 'watch' in
// order to be able to mix short watches for binary clauses (without clause
// pointer) with long watches for larger clauses on the same watcher stack.

// This union type allows to push them independently, even though we always
// need to push a header, but can optionally omit the clause.  Code to
// traverse watcher stacks becomes slightly more complicated though.

// In order to avoid switching between 'union' and 'struct' with and without
// virtual binary clauses (w/o 'NVIRTUAL' undefined) we always simply use
// this 'union' type. The actual memory operations performed do not change
// anyhow.  As drawback one can consider that, without blocking literals,
// i.e., 'NBLOCK' defined and thus also 'NVIRTUAL', watches are declared as
// unions with a single member 'clause', which clutters code slightly
// (requires to use 'watch.clause').

#ifndef NBLOCK

// The header part of a watch if blocking literals are used.

struct header
{
  bool binary;			// Binary clause.
  bool redundant;		// Relevant for statistics and logging.
  unsigned blocking;		// Blocking literal of the clause.
};

#define long_clause_watch_size 2	// Two watches per long clause.

#else

#define long_clause_watch_size 1	// One without blocking literals.

#endif

// The actual watch data structure (it is a 'union' - see discussion above).

// For Java programmers not familiar with the 'union' concept in C (or
// equivalently to variant records in Pascal) is the following explanation.

// All members of a 'union' type overlap in memory and it depends on how you
// access the 'union' (in our case as '.header' or '.clause') what data is
// read (particularly if the fields have different length in bytes).  This
// is completely unsafe though in general (breaks strong typing) and for
// instance in Pascal could be used to implement type casts.  The user has
// to make sure that the right data is accessed and this requires of course
// some additional context.

// In our case, without blocking literals ('NBLOCK' defined), the 'union'
// just hides a clause pointer.  With blocking literals (keeping 'NBLOCK'
// undefined) there are always one to two watches considered together on
// watcher stacks.  The 'binary' field of the first one determines whether
// the second one really exists (or is the start of another single or pair
// of watches).  If 'binary' is false the second watch is a clause pointer.

union watch
{
#ifndef NBLOCK
  struct header header;
#endif
  struct clause *clause;
};

// Stack of watches.

struct watches
{
  union watch *begin, *end, *allocated;
};

/*------------------------------------------------------------------------*/

// Watch a literal 'lit' in a clause with blocking literal 'other'.

#ifndef NBLOCK

static void
watch_literal (struct satch *solver, bool redundant,
	       unsigned lit, unsigned blocking, struct clause *c)
{
  assert (!solver->dense);
  struct watches *watches = solver->watches + lit;
  union watch watch;
  watch.header.binary = (c->size == 2);
  watch.header.redundant = redundant;
  watch.header.blocking = blocking;
  LOGCLS (c, "watching %s blocking %s in", LOGLIT (lit), LOGLIT (blocking));
  PUSH (*watches, watch);
  watch.clause = c;
  PUSH (*watches, watch);
}

#elif !defined(NWATCHES)

static void
watch_literal (struct satch *solver, unsigned lit, struct clause *c)
{
  assert (!solver->dense);
  struct watches *watches = solver->watches + lit;
  union watch watch;
  LOGCLS (c, "watching %s in", LOGLIT (lit));
  watch.clause = c;
  PUSH (*watches, watch);
}

#endif

#if !defined(NREDUCE) || !defined(NELIMINATION) || \
    !defined(NCHRONO) || !defined(NVIVIFICATION)

#ifndef NBLOCK

static void
unwatch_literal (struct satch *solver, unsigned lit, struct clause *c)
{
  assert (!solver->dense);
  struct watches *watches = solver->watches + lit;
  const union watch *const end = watches->end;
  union watch *q = watches->begin;
  for (;;)
    {
      assert (q != end);
#if !defined(NVIRTUAL) || defined(LOGGING)
      const union watch watch = *q++;
      const struct header header = watch.header;
#endif
#ifndef NVIRTUAL
      if (header.binary)
	continue;
#endif
      const struct clause *d = q++->clause;
      if (c == d)
	{
	  LOGCLS (c, "unwatching %s blocking %s in",
		  LOGLIT (lit), LOGLIT (header.blocking));
	  break;
	}
    }
  while (q != end)
    q[-2] = *q, q++;
  watches->end -= 2;
}

#elif !defined(NWATCHES)

static void
unwatch_literal (struct satch *solver, unsigned lit, struct clause *c)
{
  assert (!solver->dense);
  struct watches *watches = solver->watches + lit;
  const union watch *const end = watches->end;
  union watch *q = watches->begin;
  for (;;)
    {
      assert (q != end);
      const struct clause *d = q++->clause;
      if (c == d)
	{
	  LOGCLS (c, "unwatching %s in", LOGLIT (lit));
	  break;
	}
    }
  while (q != end)
    q[-1] = *q, q++;
  watches->end--;
}

#endif

#endif

#ifndef NWATCHES

// Watch first two literals in the clause.

static void
watch_clause (struct satch *solver, struct clause *c)
{
  assert (!solver->dense);
  assert (c->size > 1);
  const unsigned lit = c->literals[0];
  const unsigned other = c->literals[1];
#ifndef NBLOCK
  const bool redundant = c->redundant;
  watch_literal (solver, redundant, lit, other, c);
  watch_literal (solver, redundant, other, lit, c);
#else
  watch_literal (solver, lit, c);
  watch_literal (solver, other, c);
#endif
}

#endif

