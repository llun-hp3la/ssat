/*------------------------------------------------------------------------*/

// The following functions combine both proof tracing and checking with the
// internal checker the addition and deletion of a given clause.  For
// addition proof and checker make sure that the clause is implied (through
// unit propagation) and for deletion it is first checked that the clause
// has been added before or was added as original clause and has not been
// deleted yet (followed by actually deleting it in the proof and checker).

// Trace and check addition of the clause given as array.

static void
trace_and_check_addition (struct satch *solver,
			  size_t size, unsigned *literals, unsigned except)
{
  if (solver->proof)
    {
      start_addition_proof_line (solver);
      for (all_elements_in_array (unsigned, lit, size, literals))
	if (lit != except)
	    add_internal_literal_to_proof_line (solver, lit);
      end_proof_line (solver);
    }
#ifndef NDEBUG
  for (all_elements_in_array (unsigned, lit, size, literals))
    if (lit != except)
        checker_add_literal (solver->checker, export_literal (lit));
  checker_add_learned_clause (solver->checker);
#endif
}

// Trace and check deletion of the clause given as array.

static void
trace_and_check_deletion (struct satch *solver,
			  size_t size, unsigned *literals)
{
  if (solver->proof)
    {
      start_deletion_proof_line (solver);
      for (all_elements_in_array (unsigned, lit, size, literals))
	  add_internal_literal_to_proof_line (solver, lit);
      end_proof_line (solver);
    }
#if !defined(NDEBUG) && !defined(NLEARN)
  for (all_elements_in_array (unsigned, lit, size, literals))
      checker_add_literal (solver->checker, export_literal (lit));
  checker_delete_clause (solver->checker);
#endif
}

static void
trace_and_check_empty_addition (struct satch *solver)
{
  trace_and_check_addition (solver, 0, 0, INVALID);
}

static void
trace_and_check_unit_addition (struct satch *solver, unsigned unit)
{
  trace_and_check_addition (solver, 1, &unit, INVALID);
}

// Trace and check the temporary clause as being added.

static void
trace_and_check_temporary_addition (struct satch *solver)
{
  const size_t size = SIZE_STACK (solver->clause);
  trace_and_check_addition (solver, size, solver->clause.begin, INVALID);
}

#if !defined(NVIRTUAL) && \
  (!defined(NREDUCE) || !defined(NDEBUG) || \
   !defined(NELIMINATION))

static void
trace_and_check_binary_deletion (struct satch *solver,
				 unsigned lit, unsigned other)
{
  unsigned literals[2] = { lit, other };
  trace_and_check_deletion (solver, 2, literals);
}

#endif

#if !defined (NSTRENGTHENING) || !defined (NVIVIFICATION)

static void
trace_and_check_clause_addition (struct satch *solver,
				 struct clause *c, unsigned remove)
{
  trace_and_check_addition (solver, c->size, c->literals, remove);
}

#endif

static void
trace_and_check_clause_deletion (struct satch *solver, struct clause *c)
{
  trace_and_check_deletion (solver, c->size, c->literals);
}


