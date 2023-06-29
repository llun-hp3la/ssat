int
main (int argc, char **argv)
{
  struct ssat *volatile solver = solver_init();
  // solver options are set in config file.
  if (!solver)
    error ("failed to initialize solver");
  init_signal_handler ();
  banner (); // print solver info
  int res = sat_solve (solver);
  reset_signal_handler ();
  satch_release (solver);
  return res;
}