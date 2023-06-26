/*------------------------------------------------------------------------*/

// This is a section of rather Unix specific code which might require some
// porting effort if building on other operating systems.  On the other hand
// it is only used for diagnostic purposes and in principle can be removed.

// Process time since starting the process.

static double
process_time (void)
{
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

// The maximum amount of memory used by this process as seen by the system.

static uint64_t
maximum_resident_set_size (void)
{
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  return ((uint64_t) u.ru_maxrss) << 10;
}

// Current memory used by this process as seen by the system.  This is
// very Linux specific and will not work even on other Unix systems.

uint64_t
current_resident_set_size (void)
{
  char path[48];
  sprintf (path, "/proc/%" PRIu64 "/statm", (uint64_t) getpid ());
  FILE *file = fopen (path, "r");
  if (!file)
    return 0;
  uint64_t dummy, rss;
  int scanned = fscanf (file, "%" PRIu64 " %" PRIu64 "", &dummy, &rss);
  fclose (file);
  return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
}

