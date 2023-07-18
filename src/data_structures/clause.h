#ifndef _clause_h_INCLUDED
#define _clause_h_INCLUDED

#include "literal.h"
#include <stdbool.h>

typedef struct clause clause;

#define LD_MAX_GLUE 22u
#define MAX_GLUE ((1u<<LD_MAX_GLUE)-1)


// our clauses has 3 literals
struct clause
{
  unsigned glue:LD_MAX_GLUE;

  bool garbage:1;   // whether it's for garbage collection
  bool keep:1;      // keep or discard
  bool reason:1;    // is it a reason clause
  bool redundant:1; // is it redundant
  bool shrunken:1;  
  bool subsume:1;
  bool sweeped:1;
  bool vivify:1;

  unsigned used:2;

  unsigned searched;
  unsigned size;

  unsigned lits[3]; // vector of literals
};

#define SIZE_OF_CLAUSE_HEADER ((size_t) &((clause*)0)->searched)

#define BEGIN_LITS(C) ((C)->lits)
#define END_LITS(C) (BEGIN_LITS (C) + (C)->size)

#define all_literals_in_clause(LIT,C) \
  unsigned LIT, * LIT ## _PTR = BEGIN_LITS (C), \
                * const LIT ## _END = END_LITS (C); \
  LIT ## _PTR != LIT ## _END && ((LIT = *LIT ## _PTR), true); \
  ++LIT ## _PTR




#endif
