/*------------------------------------------------------------------------*/
// The main point of this extensive configurability is to be able to strip
// down (disable) parts of the solver state if a feature which does not need
// that part is disabled. For instance if reluctant doubling is not needed
// ('--no-stable' or '--no-restart'), then we do not want to initialize it
// during mode switching.   If we do not even have a 'reluctant' member in
// this case, the compiler will catch accidental usage.

// This way we can reduce the code really needed for a feature and as just
// described remove accidental run-time overhead related to code for a
// disabled feature.

// This approach is almost straight-forward except for the various variants
// of using VSIDS or VMTF in focused and stable mode (or if one of the
// latter is disabled), which requires two averages in the default
// configuration and maybe two queues or two heaps (or a queue in stable
// mode for '--no-focused --no-vsids').  Therefore we do have some fields
// duplicated (the arrays '...[2]' above) but we make sure that we really
// only use one if the configuration needs a particular instance.

/*------------------------------------------------------------------------*/

// We use 'unsigned (int)' as type for internal literals and variable
// indices.  Our internal variable indices start at zero and literals are
// variable indices multiplied by two. The lowest bit of a literal denotes
// its sign.  The following function maps variable indices to literals.

static unsigned
LITERAL (unsigned idx)
{
  assert (idx < (1u << 31));	// Check for overflow.
  return idx << 1;
}

// Vice-versa this function maps literals to their variable index.

static unsigned
INDEX (unsigned lit)
{
  return lit >> 1;
}

// The least significant bit of a literal is its sign.

static unsigned
SIGN_BIT (unsigned lit)
{
  return lit & 1;
}

// Values of type 'signed char' are ternary and this function translate an
// (unsigned) literal bit into a (binary) 'true' or 'false' ('1' or '-1').

static int
INT_SIGN (unsigned lit)
{
  return SIGN_BIT (lit) ? -1 : 1;
}

// Negating a literal amounts to flipping its least significant bit.

static unsigned
NOT (unsigned lit)
{
  return lit ^ 1;
}

// Note that the API uses signed integers for literals.  These signed
// external DIMACS variable indices are in the range '1..INT_MAX' and are
// mapped to internal variable indices '0..(INT_MAX-1)'.

// The mapping between internal and external literals is as follows.

// +----------------------------------------+----------------------------+
// | External signed DIMACS literals        | Internal unsigned literals |
// +----------------------------------------+----------------------------+
// |     1                                  |    0                       |
// |    -1                                  |    1                       |
// |     2                                  |    2                       |
// |    -2                                  |    3                       |
// |    ...                                 |   ...                      |
// |  INT_MAX =   (1u<<31)-1  =  2147483647 | (1u<<32)-4 = 4294967292    |
// | -INT_MAX = -((1u<<31)-1) = -2147483647 | (1u<<32)-3 = 4294967293    |
// +----------------------------------------+----------------------------+

// We use the following two invalid values as sentinel to terminate a
// clause externally or as invalid literal or invalid variable internally.

// +----------------------------------------+----------------------------+
// |     0                                  | INVALID    = (1u<<32)-1    |
// |                                        |            = 4294967295    |
// |                                        |            = UINT_MAX      |
// +----------------------------------------+----------------------------+

// For completeness, note that, there is one unused value in each case.

// +----------------------------------------+----------------------------+
// | INT_MIN = -(1u<<31)      = -2147483648 | (1u<<32)-2 = 4294967294    |
// +----------------------------------------+----------------------------+

// Here we assume that 'sizeof (unsigned) == sizeof (int)', signed integers
// are encoded in two-complement and thus 'INT_MAX == (1u<<31)-1'.

// It would be possible to also use 'int' for literals internally, but then
// iterator code would become much more complicated.  Access to positively
// and negatively indexed arrays, i.e., watches and values, would be strange
// and requires complex reallocation code too (for incremental usage).

// Thus we allow up to 'INT_MAX' variables and use the all-bits-one number
// 'INVALID' to denote invalid literals and variable indices '(1u<<32)-1'.

// By default (as long 'NBLOCK' is not defined) we use 'bit-stuffing' to
// distinguish binary clause reasons (the other literal) from real large
// clause reasons (pointer to the clause).  This technique requires that
// we use the least significant bit of a pointer as flag to distinguish this
// case and accordingly reduces the number of variables on a 32-bit system.
// We use another bit for storing the information whether such reason clause
// is redundant.  Thus on a 32-bit system the maximum number of variables is
// '2^29' (which will not be reachable on such a system anyhow) but on
// 64-bit systems we can have 'INT_MAX' variables.

#define INVALID UINT_MAX
#define INVALID_LEVEL UINT_MAX

/*------------------------------------------------------------------------*/

// Increase and decrease statistic counters with over/under-flow checking.

// For those readers not familiar with this style of C macros, note that
// that this 'do { ... } while (0)' idiom makes sure that the macro almost
// acts like a procedure (function without any return value), allows local
// variables (not here but see the macros in 'stack.h'), and still can be
// used with a semicolon after it in an 'if-then-else' statement such as
//
//   if (c->redundant) DEC (redundant); else DEC (irredundant);
//
// which would become a syntax error if we only use a block of curly
// parenthesis.  We can also 'return' early with a 'break' statement
// (instead of 'return').  An alternative consists of statement expressions,
// which however are a GCC extension and (pedantic) compilation fails for
// '-W -Wall -Werror -pedantic' on these extensions (as for the otherwise
// pretty handy 'typeof', which, accordingly, we also do not use).

#define DEC(NAME) \
do { \
  assert (solver->statistics.NAME > 0); \
  solver->statistics.NAME--; \
} while (0)

// For this macro we want to produce a 'return' value which requires a more
// sophisticated use of the 'comma' operator. Again 'statement expressions'
// would be an alternative but we do not want to use those.  This technique
// breaks down if you need more sophisticated control flow, i.e., loops.
// See 'COVER' for another use of 'comma' as well as how we define the
// anticipated loop condition in the 'all_...' iterator macros below.

#define INC(NAME) \
  ( \
    assert (solver->statistics.NAME < UINT64_MAX), \
    ++solver->statistics.NAME \
  )

#define ADD(NAME,DELTA) \
do { \
  assert (UINT64_MAX - (DELTA) >= solver->statistics.NAME); \
  solver->statistics.NAME += (DELTA); \
} while (0)

/*------------------------------------------------------------------------*/

// The number of variables and literals.

#define VARIABLES (solver->size)
#define LITERALS (2u*VARIABLES)

// We also often need the number of conflicts, decisions and ticks.

#define CONFLICTS (solver->statistics.conflicts)
#define DECISIONS (solver->statistics.decisions)
#define TICKS (solver->statistics.ticks)

/*------------------------------------------------------------------------*/

// Iterators for global solver data.  They can be used in a similar way as
// range-based for-loops in C++-11.  For instance the idiom
//
//   for (all_variables (idx))
//     ...
//
// goes over all variable indices 'idx'.

// The features of C'99 we use here are local declarations in for-loops and
// the comma-operator to assign the range variable 'idx' as side effect of a
// 'true' expression.  Similar code in 'stack.h' allows to iterate over
// generic stacks.

#define all_variables(IDX) \
  unsigned IDX = 0, END_VARIABLES = VARIABLES; IDX < END_VARIABLES; IDX++

#define all_literals(LIT) \
  unsigned LIT = 0, END_LITERALS = LITERALS; LIT < END_LITERALS; LIT++

#define all_elements_in_array(TYPE,LIT,SIZE,LITS) \
  TYPE LIT, * P_ ## LIT = (LITS), \
            * const END_ ## LIT = P_ ## LIT + (SIZE); \
  (P_ ## LIT != END_ ## LIT) && (LIT = *P_ ## LIT, true); ++P_ ## LIT

#define all_literals_in_clause(LIT,C) \
   all_elements_in_array (unsigned, LIT, (C)->size, (C)->literals)

#define all_irredundant_clauses(C) \
  all_pointers_on_stack (struct clause, C, solver->irredundant)

#define all_redundant_clauses(C) \
  all_pointers_on_stack (struct clause, C, solver->redundant)

#define all_redundant_clauses_in_reverse(C) \
  all_pointers_on_stack_in_reverse (struct clause, C, solver->redundant)

/*------------------------------------------------------------------------*/

// The 'COVER' macro is used for testing and debugging, more precisely for
// the case where full assertion checking (and proof checking) is not
// feasible, but you still want to figure out whether a certain situation
// can happen.  Those conditions 'COND' are thus 'coverage goals', i.e.,
// conditions you want to hit, or situations where you are almost 100% sure
// that they can never happen, but you want to make sure that it does not
// happen maybe accidentally during a full run on a competition set.  Trying
// to cover a certain condition during fuzzing with full optimization and no
// other (assertion) checking switched on is another common use case.

// Now to the macro itself.  This is in essence follows the same principle
// when you implement 'assert' yourself.  The main point is that it should
// be an expression of type 'void' such that you can use it as part of a
// 'comma' list.  For other examples see 'TOP' and 'POP' in 'stack.h'.

#define COVER(COND) \
( \
    (COND) \
  ? \
    ( \
      fflush (stdout), \
      fprintf (stderr, "%s:%ld: %s: Coverage goal `%s' reached.\n", \
        __FILE__, (long) __LINE__, __func__, #COND), \
      abort (), \
      (void) 0 \
    ) \
  : \
    (void) 0 \
)

/*------------------------------------------------------------------------*/

// Export internal unsigned literals as external signed literals.

static unsigned
export_literal (unsigned ilit)
{
  const unsigned iidx = INDEX (ilit);
  assert (iidx < (unsigned) INT_MAX - 1);
  const int eidx = iidx + 1;
  const int elit = SIGN_BIT (ilit) ? -eidx : eidx;
  return elit;
}

