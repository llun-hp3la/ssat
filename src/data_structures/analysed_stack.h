/*------------------------------------------------------------------------*/

// Analyzed variables (enables sorting with respect to stamps).

struct analyzed
{
  unsigned idx;
#ifndef NSORTANALYZED
  unsigned stamp;		// Needed for sorting bumped variables only.
#endif
};

/*------------------------------------------------------------------------*/

// Stack of analyzed indices with stamps.

struct analyzed_stack
{
  struct analyzed *begin, *end, *allocated;
};

