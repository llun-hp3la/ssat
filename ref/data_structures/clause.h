/*------------------------------------------------------------------------*/

// The basic clause data structure.  Note however that binary clauses are
// kept in watch lists by default if blocking literals are used (or
// equivalently 'NBLOCK' is kept undefined).

struct clause
{
#if defined(LOGGING) || defined(NRADIXSORT)

  // From 'solver->statistics.added' needed for stable sorting if radix
  // sorting is disabled ('NRADIXSORT' defined) and of course for logging.

  uint64_t id;
#endif

  // First we have boolean flags with few bits.  This way the compiler has
  // the opportunity to merge them all into a single (32-bit) word.

  bool garbage:1;		// Collect at next garbage collection.
  bool protected:1;		// Do not collect current reason clauses.
  bool redundant:1;		// Redundant / learned (not irredundant).
#ifndef NSUBSUMPTION
  bool subsumed:1;		// Already used in subsumption.
#endif
#ifndef NUSED
#ifndef NTIER2
  unsigned used:2;		// Used since last clause reduction.
#else
  unsigned used:1;		// Used since last clause reduction.
#endif
#endif
#ifndef NVIVIFICATION
  bool shrunken:1;
  unsigned vivify:2;
#endif

#ifdef NWATCHES
 unsigned sum;			// Sum of non-false literals.
 unsigned count;		// Number of non-false literals.
#endif

#ifndef NGLUE
  unsigned glue;		// Glucose level (LBD).
#endif

#ifndef NCACHE
  unsigned search;		// Cached replacement search position.
#endif

  unsigned size;		// Size of clause (number of literals).

#ifndef NVARIADIC

  // This default version 'embeds' the literals directly into the clause.
  // Then the literals follow the clause header directly in memory.  This
  // makes the size of the actual memory block of a clause 'variadic'.

  unsigned literals[2];
#else

  // This non-variadic version stores the literals separately which requires
  // another rather expensive pointer dereference accessing the literals.

  unsigned *literals;
#endif
};

/*------------------------------------------------------------------------*/

// Stack of clause pointers.

struct clauses
{
  struct clause **begin, **end, **allocated;
};

/*------------------------------------------------------------------------*/

// Allocate the actual clause data memory and depending on whether we embed
// the literals directly into the clause using a variadic array member just
// allocate one chunk of memory or otherwise the literals separately.

#ifndef NVARIADIC

static size_t
bytes_clause (size_t size)
{
  assert (size > 1);
  return sizeof (struct clause) + (size - 2) * sizeof (unsigned);
}

// This default variadic variant just allocates one chunk of memory.

static struct clause *
allocate_clause (size_t size)
{
  const size_t bytes = bytes_clause (size);
  struct clause *res = malloc (bytes);
  if (!res)
    out_of_memory (bytes);
  return res;
}

static size_t
deallocate_clause (struct clause *c)
{
  const size_t bytes = bytes_clause (c->size);
  free (c);
  return bytes;
}

#else

// The non-variadic variant has to allocate two memory blocks.

static struct clause *
allocate_clause (size_t size)
{
  const size_t header_bytes = sizeof (struct clause);
  struct clause *res = malloc (header_bytes);
  if (!res)
    out_of_memory (header_bytes);
  const size_t literals_bytes = size * sizeof (unsigned);
  res->literals = malloc (literals_bytes);
  if (!res->literals)
    out_of_memory (literals_bytes);
  return res;
}

static size_t
deallocate_clause (struct clause *c)
{
  const size_t header_bytes = sizeof (struct clause);
  const size_t literals_bytes = c->size * sizeof (unsigned);
  free (c->literals);
  free (c);
  return header_bytes + literals_bytes;
}

#endif

/*------------------------------------------------------------------------*/

// Adding and deleting clauses.

// We start with the shared clause allocation function 'add_clause'.

static struct clause *
#ifndef NGLUE
add_clause (struct satch *solver, bool redundant, unsigned glue)
#else
add_clause (struct satch *solver, bool redundant)
#endif
{
#if defined(LOGGING) || defined(NRADIXSORT)
  const uint64_t added =
#endif
    INC (added);
  const size_t size = SIZE_STACK (solver->clause);
#ifdef NVIRTUAL
  assert (size > 1);		// Units and empty clauses are implicit.
#else
  assert (size > 2);		// No binary clauses allocated at all!
#endif
  struct clause *res = allocate_clause (size);
#if defined(LOGGING) || defined(NRADIXSORT)
  res->id = added;
#endif
  res->garbage = false;
  res->protected = false;
  res->redundant = redundant;
#ifndef NUSED
  res->used = 0;
#endif
#ifndef NSUBSUMPTION
  res->subsumed = false;
#endif
#ifdef NWATCHES
  res->sum = 0;
  res->count = 0;
#endif
#ifndef NGLUE
  res->glue = glue;
#endif
#ifndef NCACHE
  res->search = 0;
#endif
  res->size = size;
#ifndef NVIVIFICATION
  res->vivify = 0;
  res->shrunken = false;
#endif
  memcpy (res->literals, solver->clause.begin, size * sizeof (unsigned));
  return res;
}

static struct clause *
new_irredundant_clause (struct satch *solver)
{
#ifndef NGLUE
  struct clause *res = add_clause (solver, false, 0);
#else
  struct clause *res = add_clause (solver, false);
#endif
  PUSH (solver->irredundant, res);
  INC (irredundant);
  return res;
}

#ifndef NCDCL
static struct clause *
#ifndef NGLUE
new_redundant_clause (struct satch *solver, unsigned glue)
#else
new_redundant_clause (struct satch *solver)
#endif
{
#ifndef NGLUE
  struct clause *res = add_clause (solver, true, glue);
#else
  struct clause *res = add_clause (solver, true);
#endif
#ifndef NLEARN
  PUSH (solver->redundant, res);
#endif
  INC (redundant);
  return res;
}
#endif

// Deleting clauses beside deallocation implicitly also triggers adding a
// deletion line to the proof (if tracing is enabled) and in debugging
// compilation mode also deletes the clause from the internal proof checker.

// This is in contrast to adding clauses to the proof and the checker which
// has to be done explicitly by the caller of the 'new_...' functions above.

static size_t
delete_clause (struct satch *solver, struct clause *c)
{
  INC (deleted);
  LOGCLS (c, "delete");
  if (!c->garbage)
    {
      trace_and_check_clause_deletion (solver, c);
      if (c->redundant)
	DEC (redundant);
      else
	DEC (irredundant);
    }
  return deallocate_clause (c);
}

#ifndef NBLOCK

// With blocking literals we do not have to store clauses as reasons. At the
// same time (since this is used for compact watch data structures anyhow)
// we also use the temporary binary clause for conflicting binary clauses.

static void
init_binary (struct satch *solver)
{
  for (unsigned i = 0; i < 2; i++)
    {
      struct clause *binary = solver->binary + i;
      binary->size = 2;
#ifdef NVARIADIC
      const size_t bytes = 2 * sizeof (unsigned);
      if (!(binary->literals = malloc (bytes)))
	out_of_memory (bytes);
#endif
    }
}

static void
release_binary (struct satch *solver)
{
#ifdef NVARIADIC
  for (unsigned i = 0; i < 2; i++)
    free (solver->binary[i].literals);
#else
  (void) solver;		// Prevent unused 'solver' warning.
#endif
}

// Copy 'lit' and 'other' to one of the two temporary binary clauses in the
// solver.  This is used for generating a binary clause conflict (if
// 'NBLOCK' is undefined) and through 'untag_clause' to unify the conflict
// analysis code with and without 'NBLOCK'.

static struct clause *
binary_clause (struct satch *solver, unsigned pos,
	       bool redundant, unsigned lit, unsigned other)
{
  assert (pos == 0 || pos == 1);
  struct clause *res = solver->binary + pos;
  assert (!res->garbage);
  assert (res->size == 2);
  res->redundant = redundant;
  res->literals[0] = lit;
  res->literals[1] = other;
  return res;
}

/*------------------------------------------------------------------------*/

// We want to only have one global 'reason' array in which we store both
// binary clause reasons (which consists of just the other literal) as well
// as pointers to large clause.  We distinguish those by 'stuffing' a bit
// into the clause pointer.  In case the least-significant bit is set then
// the rest of the 'reason' pointer forms the other literal.  Otherwise it
// is the actual pointer to a large clause.

// Note that the least two significant bits of a pointer are zero on all
// systems we have seen and this is a common idiom anyhow (for instance in
// AIG and BDD packages). For logging we thus can also use the second least
// significant bit for storing whether the binary (reason) is redundant.

// Some technical details follow on why this scheme works perfectly well on
// 64-bit machines.  On such machines pointer size is twice the size of
// 'unsigned' literals and the 32-bit variable-index easily fits into the
// upper 62 bits of a reason pointer.  On 32-bit machines this might break
// for literals larger equal to 2^30 which is however prevented by raising
// an API contract violation, when trying to import a variable of size
// larger than 2^29.  Thus on 32-bit machines we 'only' have 2^29 variables.
// Trying to reach this limit on a 32-bit machine would probably lead to
// a memory overflow much earlier anyhow.

static bool
is_tagged_clause (const struct clause *const c)
{
  uintptr_t word = (uintptr_t) c;
  return !!(word & 3);
}

static struct clause *
tag_binary_clause (bool redundant, uintptr_t other)
{
  const uintptr_t tmp = (other << 2) | 1 | (redundant << 1);
  struct clause *res = (struct clause *) tmp;
  assert (is_tagged_clause (res));
  return res;
}

static unsigned
tagged_clause_to_literal (const struct clause *c)
{
  assert (is_tagged_clause (c));
  const uintptr_t tmp = (uintptr_t) c;
  const unsigned res = tmp >> 2;
  return res;
}

static unsigned
tagged_clause_to_redundant (const struct clause *c)
{
  assert (is_tagged_clause (c));
  const uintptr_t tmp = (uintptr_t) c;
  const bool res = !!(tmp & 2);
  return res;
}

#if defined(LOGGING)

static void
logging_tagged (struct satch *solver, unsigned lit,
		struct clause *c, const char *fmt, ...)
{
  const unsigned other = tagged_clause_to_literal (c);
  const bool redundant = tagged_clause_to_redundant (c);
  logging_prefix (solver);
  logging_format (fmt);
  if (redundant)
    printf (" redundant");
  else
    printf (" irredundant");
  printf (" binary clause %s %s", LOGLIT (lit), LOGLIT (other));
  logging_suffix ();
}

#endif

static struct clause *
untag_clause (struct satch *solver,
	      unsigned pos, unsigned lit, const struct clause *c)
{
  assert (is_tagged_clause (c));
  const unsigned other = tagged_clause_to_literal (c);
  const bool redundant = tagged_clause_to_redundant (c);
  return binary_clause (solver, pos, redundant, lit, other);
}

#endif

