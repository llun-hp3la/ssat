/*------------------------------------------------------------------------*/

// Print DRAT (actually DRUP) proof lines to the given proof file.

// These lines are either clause additions or clause deletions and either a
// binary or ASCII format is used.  The binary format distinguishes
// additions from deletions by a leading 'a' respectively 'd' (ASCII)
// character, while the ASCII format just adds a 'd ' prefix (note the space
// after 'd') for clause deletion.

// After that the literals are printed.  The binary format uses a dynamic
// word length for numbers while the ASCII format looks like the DIMACS
// format. The end of a proof line is indicated by zero (then number zero
// '0' in the ASCII format and the zero byte in the binary format).

static void
start_addition_proof_line (struct satch *solver)
{
  assert (solver->proof);
  if (!solver->options.ascii)
    fputc ('a', solver->proof);
}

static void
start_deletion_proof_line (struct satch *solver)
{
  assert (solver->proof);
  fputc ('d', solver->proof);
  if (solver->options.ascii)
    fputc (' ', solver->proof);
}

static void
add_external_literal_to_proof_line (struct satch *solver, int elit)
{
  assert (solver->proof);
  if (solver->options.ascii)
    fprintf (solver->proof, "%d ", elit);
  else
    {
      // This is almost like our internal literal encoding except that it is
      // shifted by two, since zero is used as sentinel of a proof line.

      assert (2u * INT_MAX + 1 == UINT_MAX);	// Overflow for 'INT_MAX'.

      const unsigned plit = 2u * abs (elit) + (elit < 0);

      // Now this proof literal 'plit' is written 7-bit wise to the file.

      // The 8th most significant bit of the actual written byte denotes
      // whether further non-zero bits, so at least one more byte, follow.

      unsigned rest = plit;

      while (rest & ~0x7f)
	{
	  const unsigned char byte = (rest & 0x7f) | 0x80;
	  fputc (byte, solver->proof);
	  rest >>= 7;
	}

      fputc ((unsigned char) rest, solver->proof);
    }
}

static void
add_internal_literal_to_proof_line (struct satch *solver, unsigned ilit)
{
  const int elit = export_literal (ilit);
  add_external_literal_to_proof_line (solver, elit);
}

static void
end_proof_line (struct satch *solver)
{
  assert (solver->proof);
  if (solver->options.ascii)
    fputs ("0\n", solver->proof);
  else
    fputc (0, solver->proof);
  fflush (solver->proof);
}

