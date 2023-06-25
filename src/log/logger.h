#ifdef LOGGING

// Logging functions are only compiled in debugging mode and then still need
// to be enabled at run-time (with '-l' or 'satch_enable_logging_messages').

static void
logging_prefix (struct satch *solver)
{
  COLORS (1);
  COLOR (MAGENTA);
  assert (solver->options.logging);
  printf ("c LOG %u ", solver->level);
}

#define logging_format(fmt) \
do { \
  va_list ap; \
  va_start (ap, fmt); \
  vprintf (fmt, ap); \
  va_end (ap); \
} while (0)

static void
logging_suffix (void)
{
  COLORS (1);
  COLOR (NORMAL);
  fputc ('\n', stdout);
  fflush (stdout);
}

// This is the function for default log messages from the 'LOG' macro.
// It prints the SAT-competition comment-line prefix 'c', the string 'LOG',
// then the decision level and finally the actual logging message, all
// separated by spaces.

static void
logging_message (struct satch *solver, const char *fmt, ...)
{
  logging_prefix (solver);
  logging_format (fmt);
  logging_suffix ();
}

static size_t
format_literal (struct satch *solver, char *res, unsigned ilit)
{
  const int tmp = solver->values[ilit];
  const int elit = export_literal (ilit);

  if (!tmp)
    return sprintf (res, "%u(%d)", ilit, elit);

  const unsigned iidx = INDEX (ilit);
  const unsigned level = solver->levels[iidx];
  return sprintf (res, "%u(%d)@%u=%d", ilit, elit, level, tmp);
}

static char *
next_format (struct satch *solver)
{
  char *res = solver->format[solver->next_format++];

  if (solver->next_format == sizeof solver->format / sizeof solver->format[0])
    solver->next_format = 0;

  return res;
}

static const char *
logging_literal (struct satch *solver, unsigned lit)
{
  char *res = next_format (solver);
  (void) format_literal (solver, res, lit);
  return res;
}

static const char *
logging_variable (struct satch *solver, unsigned idx)
{
  char *res = next_format (solver);
  char *tmp = res + sprintf (res, "variable %u literal ", idx);
  const unsigned lit = LITERAL (idx);
  (void) format_literal (solver, tmp, lit);
  return res;
}

#define LOGLIT(LIT) logging_literal (solver, (LIT))
#define LOGVAR(IDX) logging_variable (solver, (IDX))

#ifndef NVIRTUAL

// For virtual binary clauses we need special logging functions too.

static void
logging_binary (struct satch *solver,
		bool redundant, unsigned lit, unsigned other,
		const char *fmt, ...)
{
  logging_prefix (solver);
  logging_format (fmt);
  if (redundant)
    printf (" redundant");
  else
    printf (" irredundant");
  printf (" binary clause %s %s", LOGLIT (lit), LOGLIT (other));
  logging_suffix ();
}

#endif

// After printing in essence the same message as the basic logging function
// above this clause logging function conveniently prints the type of the
// clause given as argument, its glue (if redundant), its size and literals.

static void
logging_clause (struct satch *solver, struct clause *c, const char *fmt, ...)
{
  logging_prefix (solver);
  logging_format (fmt);
#ifdef NCDCL
  if (c == DUMMY_REASON) {
    printf ("dummy decision clause");
  }
  else
#endif
    {
#ifndef NBLOCK
      // With blocking literals enabled we use the temporary binary clause for
      // binary reasons and binary conflicts.  This clause needs special
      // treatment here since its identifier is invalid (always zero).
      if (is_temporary_binary (solver, c))
        printf (" temporary binary clause");
      else
#endif
        {
          if (c->redundant)
            {
              printf (" redundant");
#ifndef NGLUE
              printf (" glue %u", c->glue);
#endif
            }
          else
            printf (" irredundant");
          printf (" size %u clause[%" PRIu64 "]", c->size, c->id);
        }
      for (all_literals_in_clause (lit, c))
        printf (" %s", LOGLIT (lit));
#ifdef NWATCHES
      printf (" count: %d", c->count);
#endif
    }
  logging_suffix ();
}

// The temporary clause 'solver->clause' is logged here.

static void
logging_temporary (struct satch *solver, const char *fmt, ...)
{
  logging_prefix (solver);
  logging_format (fmt);
  printf (" size %zu temporary clause", SIZE_STACK (solver->clause));
  for (all_elements_on_stack (unsigned, lit, solver->clause))
      printf (" %s", LOGLIT (lit));
  logging_suffix ();
}

#define LOG(...) \
do { \
  if (solver->options.logging) \
    logging_message (solver, __VA_ARGS__); \
} while (0)

#ifndef NVIRTUAL

// Log binary clauses (give the two literals first).

#define LOGBIN(...) \
do { \
  if (solver->options.logging) \
    logging_binary (solver, __VA_ARGS__); \
} while (0)

#endif

#ifndef NBLOCK

#define LOGTAGGED(...) \
do { \
  if (solver->options.logging) \
    logging_tagged (solver, __VA_ARGS__); \
} while (0)

#endif

// Log large clauses (first argument is the clause).

#define LOGCLS(...) \
do { \
  if (solver->options.logging) \
    logging_clause (solver, __VA_ARGS__); \
} while (0)

// Log the temporary clause in the solver.

#define LOGTMP(...) \
do { \
  if (solver->options.logging) \
    logging_temporary (solver, __VA_ARGS__); \
} while (0)

#else

// Make sure not to include logging code if 'LOGGING' is undefined.

#define LOG(...) do { (void) solver; } while(0)
#define LOGBIN(...) do { (void) solver; } while(0)
#define LOGTAGGED(...) do { (void) solver; } while(0)
#define LOGCLS(...) do { (void) solver; } while(0)
#define LOGTMP(...) do { (void) solver; } while(0)

#endif

