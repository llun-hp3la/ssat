/*------------------------------------------------------------------------*/

// *INDENT-OFF*

static const char * usage =

"usage: gencombi [ <option> ] [ <k> ]\n"
"\n"
"where '<option>' is\n"
"\n"
"  -h | --help     print this command line option summary\n"
"  -a | --all      print all possible combinations of options up to '<k>'\n"
"  -d | --dimacs   CNF encoding all pairs for '<k>'\n"
"  -i | --invalid  only print invalid combinations\n"
"  -u | --unsorted do not sort configurations\n"
"  -v | --verbose  set verbose mode\n"
"  -w | --weak     do not enforce absence of pairs\n"
"\n"
"This is a tool to generate a list of configuration options. The list of\n"
"possible options as well as incompatible pairs are hard-coded into the\n"
"program at compile time at this point.\n"
"\n"
"By default the SAT solver SATCH is used to search for a list of as few\n"
"as possible configurations which contain all valid pairs of options and\n"
"prints them. For all pair of options we also add a constraint that their\n"
"combination should not occur in at least one chosen configuration.\n"
"\n"
"Using '--all' or '-a' generates all valid combinations of options by\n"
"combining at most '<k>' options.  Again all configurations are printed.\n"
"\n"
"The third mode produces a CNF in DIMACS format which is satisfiable if\n"
"the '<k>' configurations cover all pairs of valid options.\n"
;

// *INDENT-ON*

/*------------------------------------------------------------------------*/

// This part is in essence a hard / compile-time coded set of options, the
// list of incompatible / invalid pairs of options and abbreviations for
// printing options (which is kind of redundant since we could have put the
// abbreviations directly into the list of options).

static const char *options[] = {

  // Basic options ordered with most likely failing compilation first.

  "--pedantic", "--debug", "--check", "--symbols", "--logging",

  // Two options which are only enabled for '--debug'.

  "--no-check",
#define LAST_HARD_CODED_OPTION "--no-logging"
  LAST_HARD_CODED_OPTION,

  // Options to disable features sorted alphabetically.  During
  // initialization 'features' is set to point to the first.

#include "features/list.h"

  0				// Zero sentinel
};

// Pairs of implied / incompatible options (sorted alphabetically also
// within the individual pairs).

static const char *incompatible[] = {

  "--check", "--debug",
  "--check", "--no-check",
  "--debug", "--logging",
  "--debug", "--symbols",
  "--logging", "--no-logging",

#include "features/invalid.h"

  0,				// Zero sentinel.

};



int
main (int argc, char **argv)
{
    struct solver_configuration_options opt = parse_solver_config_option(**argv); // parse solver option which will be converted to a k-SAT problem
    return 0;
}