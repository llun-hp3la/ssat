/*------------------------------------------------------------------------*/

// Pre-allocated stack of literals with 'propagate' to perform breadth-first
// search over assigned literals on the trail during propagation.

struct trail
{
  unsigned *begin, *end;	// As in 'stack' (can use stack macros).
  unsigned *propagate;		// Position of next literal to propagate.
};

#ifndef NCONTROL
struct level
{
  unsigned * trail; // trail start of this level
  unsigned lvl;
  struct {
    unsigned earliest;
    unsigned count;
  } seen;
};

struct control
{
  struct level *begin, *end, *allocated;	// As in 'stack' (can use stack macros).
};
#endif
