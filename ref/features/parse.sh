# Automatically generated by 'features/generate'.

# Match options which disable features.

parse () {
  res=0
  case x"$1" in
    x"--no-best") best=no;;
    x"--no-block") block=no;;
    x"--no-bump") bump=no;;
    x"--no-bump-reasons") bumpreasons=no;;
    x"--no-cache") cache=no;;
    x"--no-cdcl") cdcl=no;;
    x"--no-cheapprofiling") cheapprofiling=no;;
    x"--no-chrono") chrono=no;;
    x"--no-chronoreuse") chronoreuse=no;;
    x"--no-color") color=no;;
    x"--no-control") control=no;;
    x"--no-elimination") elimination=no;;
    x"--no-elimination-limits") eliminationlimits=no;;
    x"--no-focused") focused=no;;
    x"--no-glue") glue=no;;
    x"--no-inprocessing") inprocessing=no;;
    x"--no-inverted") inverted=no;;
    x"--no-lazy-activation") lazyactivation=no;;
    x"--no-learn") learn=no;;
    x"--no-limits") limits=no;;
    x"--no-minimize") minimize=no;;
    x"--no-radix-sort") radixsort=no;;
    x"--no-reduce") reduce=no;;
    x"--no-rephase") rephase=no;;
    x"--no-restart") restart=no;;
    x"--no-reuse") reuse=no;;
    x"--no-reusestable") reusestable=no;;
    x"--no-save") save=no;;
    x"--no-shrink") shrink=no;;
    x"--no-simplification") simplification=no;;
    x"--no-sort-analyzed") sortanalyzed=no;;
    x"--no-sort-deduced") sortdeduced=no;;
    x"--no-stable") stable=no;;
    x"--no-strengthening") strengthening=no;;
    x"--no-subsumption") subsumption=no;;
    x"--no-subsumption-limits") subsumptionlimits=no;;
    x"--no-target") target=no;;
    x"--no-tier1") tier1=no;;
    x"--no-tier2") tier2=no;;
    x"--no-true") true=no;;
    x"--no-used") used=no;;
    x"--no-variadic") variadic=no;;
    x"--no-virtual") virtual=no;;
    x"--no-vivification") vivification=no;;
    x"--no-vivificationlimits") vivificationlimits=no;;
    x"--no-vivifyimply") vivifyimply=no;;
    x"--no-vmtf") vmtf=no;;
    x"--no-vsids") vsids=no;;
    x"--no-watches") watches=no;;
    *) res=1;;
  esac
  return $res
}
