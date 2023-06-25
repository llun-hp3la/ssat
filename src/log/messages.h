/*------------------------------------------------------------------------*/

// These declarations provide nice warning messages if these functions are
// used with format strings which do not match the type of an argument,
// which otherwise is very hard to get right (particularly for logging).

static void fatal_error (const char *fmt, ...)
  __attribute__((format (printf, 1, 2)));

// As with 'NLIMITS' above we want to have a central place where we filter
// out cases where message code is not included and then define 'NMESSAGE.

#ifdef NBUMP
#ifdef NELIMINATION
#ifdef NSWITCH
#ifdef NREDUCE
#ifdef NREPHASE
#ifdef NRESTART
#ifdef NTARGET
#define NMESSAGE
#endif
#endif
#endif
#endif
#endif
#endif
#endif

#ifndef NMESSAGE

static void message (struct satch *,
		     unsigned level, const char *name, uint64_t count,
		     const char *fmt, ...)
  __attribute__((format (printf, 5, 6)));

#endif

#ifdef LOGGING

static void logging_message (struct satch *, const char *fmt, ...)
  __attribute__((format (printf, 2, 3)));

#ifndef NVIRTUAL

static void logging_binary (struct satch *solver,
			    bool redundant, unsigned lit, unsigned other,
			    const char *fmt, ...)
  __attribute__((format (printf, 5, 6)));

#endif

#ifndef NBLOCK

static void logging_tagged (struct satch *solver, unsigned lit,
			    struct clause *, const char *fmt, ...)
  __attribute__((format (printf, 4, 5)));

#endif

static void logging_clause (struct satch *, struct clause *,
			    const char *fmt, ...)
  __attribute__((format (printf, 3, 4)));

static void logging_temporary (struct satch *, const char *fmt, ...)
  __attribute__((format (printf, 2, 3)));

#endif

/*------------------------------------------------------------------------*/

// This section contains error, verbose and logging messages.

// Fatal error message printed to '<stderr>' followed by an 'abort' call.

static void
fatal_error (const char *fmt, ...)
{
  COLORS (2);
  va_list ap;
  fprintf (stderr, "%slibsatch: %sfatal error: %s", BOLD, RED, NORMAL);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  abort ();
}

// Running out-of-memory is a common fatal error message.

static void
out_of_memory (size_t bytes)
{
  fatal_error ("out-of-memory allocating %zu bytes", bytes);
}

#ifndef NMESSAGE

// Print a verbose message with the given verbose level.

static void
message (struct satch *solver,
	 unsigned level, const char *name, uint64_t count,
	 const char *fmt, ...)
{
  if (solver->options.verbose < level)
    return;
  fputs ("c ", stdout);
  printf ("[%s-%" PRIu64 "] ", name, count);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#endif

// Print nicely formatted 'c ---- [ <name> ] ----- ... ' section start line.

static void
internal_section (struct satch *solver, const char *name)
{
  assert (solver);
  if (solver->statistics.sections)
    fputs ("c\n", stdout);
  INC (sections);
  COLORS (1);
  fputs ("c ", stdout);
  COLOR (BLUE);
  fputs ("---- [ ", stdout);
  COLOR (BOLD);
  fputs (name, stdout);
  COLOR (NORMAL);
  COLOR (BLUE);
  fputs (" ] ", stdout);
  for (size_t i = strlen (name); i < 66; i++)
    putc ('-', stdout);
  COLOR (NORMAL);
  fputs ("\nc\n", stdout);
  fflush (stdout);
}

#if (!defined(NBLOCK) && \
     (defined(LOGGING) || !defined(NUSED) || !defined(NCHRONO))) || \
    (!defined(NVIRTUAL) && (!defined(NDEBUG) || !defined(NSUBSUMPTION)))

static bool
is_temporary_binary (struct satch *solver, struct clause *c)
{
  return c == solver->binary || c == solver->binary + 1;
}

#endif

