#ifndef NELIMINATION

// Variables which occur in an irredundant clause which is deleted are
// marked as candidates for variable eliminations.

// For instance if a unit clause is learned during search and an irredundant
// clauses becomes satisfied and then during reduction is removed, the other
// variables in such a clause should be retried to be eliminated in the next
// variable elimination round since they now occur less often.

// We also use the 'marked_eliminate' counter to wait in 'eliminating' until
// we really have a chance to eliminate a new variable.

// We have to put this code early since clause deletion calls it.

static void
mark_eliminate_literal (struct satch *solver, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  struct flags *f = solver->flags + idx;
  if (!f->active)
    return;
  if (f->eliminate)
    return;
  LOG ("marking %s as elimination candidate", LOGVAR (idx));
  f->eliminate = true;
  INC (marked_eliminate);
}

static void
mark_eliminate_clause (struct satch *solver, struct clause *c)
{
  for (all_literals_in_clause (lit, c))
    mark_eliminate_literal (solver, lit);
}

#endif

#if !defined(NSUBSUMPTION) && (!defined(NREDUCE) || !defined(NELIMINATION))

// For subsumption a similar approach is used, except that variables are
// considered subsumption candidates if an irredundant clause is added.

static void
mark_subsume_variable (struct satch *solver, unsigned idx)
{
  struct flags *f = solver->flags + idx;
  if (!f->active)
    return;
  if (f->subsume & 1)
    return;
  LOG ("marking %s as subsume candidate", LOGVAR (idx));
  f->subsume |= 1;
  INC (marked_subsume);
}


static void
mark_subsume_literal (struct satch *solver, unsigned lit)
{
  const unsigned idx = INDEX (lit);
  mark_subsume_variable (solver, idx);
}

#endif

/*------------------------------------------------------------------------*/
