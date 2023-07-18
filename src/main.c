
struct ssat *volatile solver;

// The main CDCL loop in kissat, we wish to change the solver inner data structure so it can solve large problem, and communicate easily when runnning in parallel
static int
CDCL (ssat * solver)
{
  start_search (solver);
  int res = solver->inconsistent ? 20 : 0;
  while (!res)
    {
      clause *conflict = search_propagate (solver);
      if (conflict)
	res = sat_analyze (solver, conflict);
      else if (solver->iterating)
	iterate (solver);
      else if (!solver->unassigned)
	res = 10;
      else if (TERMINATED (search_terminated_1))
	break;
      else if (conflict_limit_hit (solver))
	break;
      else if (sat_reducing (solver))
	res = sat_reduce (solver);
      else if (sat_switching_search_mode (solver))
	sat_switch_search_mode (solver);
      else if (sat_restarting (solver))
	sat_restart (solver);
      else if (sat_rephasing (solver))
	sat_rephase (solver);
      else if (sat_eliminating (solver))
	res = sat_eliminate (solver);
      else if (sat_probing (solver))
	res = sat_probe (solver);
      else if (decision_limit_hit (solver))
	break;
      else
	sat_decide (solver);
    }
  stop_search (solver, res);
  return res;
}

static int
sat_solve (ssat * solver,
		 int argc, char **argv, bool *cancel_alarm_ptr)
{
  *cancel_alarm_ptr = false;
  if (argc == 2)
    if (parsed_one_option_and_return_zero_exit_code (argv[1]))
      return 0;
  application application;
  init_app (&application, solver);
  bool ok = parse_options (&application, argc, argv);
  if (application.time > 0)
    *cancel_alarm_ptr = true;
  if (!ok)
    return 1;
#ifndef QUIET
  kissat_section (solver, "banner");
  if (!GET_OPTION (quiet))
    {
      kissat_banner ("c ", SOLVER_NAME);
      fflush (stdout);
    }
#endif
#ifndef NPROOFS
  if (!write_proof (&application))
    return 1;
#endif
  if (!parse_input (&application))
    {
#ifndef NPROOFS
      close_proof (&application);
#endif
      return 1;
    }
#ifndef QUIET
#ifndef NOPTIONS
  print_options (solver);
#endif
  print_limits (&application);
  kissat_section (solver, "solving");
#endif
  int res = kissat_solve (solver);
  if (res)
    {
      kissat_section (solver, "result");
      if (res == 20)
	{
	  printf ("s UNSATISFIABLE\n");
	  fflush (stdout);
	}
      else if (res == 10)
	{
#ifndef NDEBUG
	  if (GET_OPTION (check))
	    kissat_check_satisfying_assignment (solver);
#endif
	  printf ("s SATISFIABLE\n");
	  fflush (stdout);
	  if (application.witness)
	    kissat_print_witness (solver,
				  application.max_var, application.partial);
	}
    }
#ifndef QUIET
  kissat_print_statistics (solver);
#endif
#ifndef NPROOFS
  close_proof (&application);
#endif
#ifndef QUIET
  kissat_section (solver, "shutting down");
  kissat_message (solver, "exit %d", res);
#endif
  return res;
}

int
main (int argc, char **argv)
{
  solver = solver_init();
  // solver options are set in config file.
  if (!solver)
    error ("failed to initialize solver");    
  kissat_init_alarm (kissat_alarm_handler);      
  kissat_init_signal_handler (kissat_signal_handler);
  banner (); // print solver info
  int res = sat_solve (solver);
  reset_signal_handler ();
  sat_release (solver);
#ifndef NDEBUG
  if (!res)
    return dump (0);
#endif
  return res;
}