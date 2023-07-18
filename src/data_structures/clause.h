#ifndef _clause_h_INCLUDED
#define _clause_h_INCLUDED

#include "literal.h"
#include <stdbool.h>

typedef struct clause clause;

#define LD_MAX_GLUE 22u
#define MAX_GLUE ((1u<<LD_MAX_GLUE)-1)


// our clauses has 3 literals
// we use bitfield in our declaration of this data structure
struct clause
{
  unsigned glue:LD_MAX_GLUE; // use 22 bits
  bool garbage:1;   // whether it's for garbage collection
  bool keep:1;      // keep or discard
  bool reason:1;    // is it a reason clause
  bool redundant:1; // is it redundant
  bool shrunken:1;  
  bool subsume:1;
  bool sweeped:1;
  bool vivify:1;
  unsigned used:2;  // use 2 bits

  unsigned searched;
  unsigned size;

  unsigned lits[3]; // vector of literals
}; // total of 24 bytes

#define SIZE_OF_CLAUSE_HEADER ((size_t) &((clause*)0)->searched)

#define BEGIN_LITS(C) ((C)->lits)
#define END_LITS(C) (BEGIN_LITS (C) + (C)->size)

#define all_literals_in_clause(LIT,C) \
  unsigned LIT, * LIT ## _PTR = BEGIN_LITS (C), \
                * const LIT ## _END = END_LITS (C); \
  LIT ## _PTR != LIT ## _END && ((LIT = *LIT ## _PTR), true); \
  ++LIT ## _PTR

static inline size_t
kissat_bytes_of_clause (unsigned size)
{
  const size_t res = sizeof (clause) + (size - 3) * sizeof (unsigned);
  return kissat_align_ward (res); // size of clause is a multiple of 8 or 16
}

static inline size_t
kissat_actual_bytes_of_clause (clause * c)
{
  unsigned const *p = END_LITS (c);
  if (c->shrunken)
    while (*p++ != INVALID_LIT)
      ;
  return kissat_align_ward ((char *) p - (char *) c);
}

static inline clause *
kissat_next_clause (clause * c)
{
  word bytes = kissat_actual_bytes_of_clause (c);
  return (clause *) ((char *) c + bytes);
}


#endif
