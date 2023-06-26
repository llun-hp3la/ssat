/*------------------------------------------------------------------------*/

// Computing the percentage or 'relative' average between two numbers is
// very common and always needs to be guarded against division by zero.
// Therefore we factor out this check into two simple functions which also
// makes the caller code (usually) more readable.

static double
percent (double a, double b)
{
  return b ? 100.0 * a / b : 0;
}

static double
relative (double a, double b)
{
  return b ? a / b : 0;
}

