/*------------------------------------------------------------------------*/

#ifndef NQUEUE

// Links for doubly-linked variable decision queue.

struct link
{
  unsigned prev;		// Previous variable index.
  unsigned next;		// Next variable index
  unsigned stamp;		// Enqueue time stamp.
};

/*------------------------------------------------------------------------*/

// Variable move-to-front doubly-linked list decision queue.

struct queue
{
  struct link *links;		// Variable links in decision queue.
  unsigned size;		// Size of queue (when last used).
  unsigned first;		// First enqueued variable index.
  unsigned last;		// Last enqueued variable index.
  unsigned search;		// Cache search in 'decide'.
  unsigned stamp;		// Enqueue time stamp.
};

#endif

/*------------------------------------------------------------------------*/

#ifndef NHEAP

// Priority queue with (E)VSIDS scores implemented as binary heap.

struct heap
{
  unsigned *begin, *end;	// Pre-allocated stack of variables.
  unsigned *pos;		// Pre-allocated variable to position map.
  double *score;		// The actual score of the variable.
  unsigned size;		// Size of heap (when last used).
  double increment;		// Exponentially increasing score increment.
  double factor;		// Increased by this factor.
};

#endif

