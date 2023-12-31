# Automatically generated by 'features/generate'.

# Print option usage to disable features.

cat<<EOF
--no-best               disable best trail rephasing (in stable mode)
--no-block              disable blocking literals (thus slower propagation)
--no-bump               disable variable bumping (during conflict analysis)
--no-bump-reasons       disable bumping of reason side literals
--no-cache              disable caching searched replacements in clauses
--no-cdcl               disable learning and backjumping (pure DPLL)
--no-cheapprofiling     enable expansive profiling
--no-chrono             disable chronological backtracking
--no-chronoreuse        jump only to the last level
--no-color              disable colored outputs for terminals
--no-control            use control structure for the trail
--no-elimination        disable bounded variable elimination
--no-elimination-limits disable size, occurrence and round limits
--no-focused            disable focused mode and always use stable mode
--no-glue               disable glue based clause reduction (use size only)
--no-inprocessing       disable inprocessing but enable preprocessing
--no-inverted           disable inverted target rephasing (in stable mode)
--no-lazy-activation    disable activating variables lazily
--no-learn              disable clause learning (no learned clauses)
--no-limits             disable subsumption and elimination limits
--no-minimize           disable clause minimization (of 1st UIP clause)
--no-radix-sort         disable radix-sorting of literals and clauses
--no-reduce             disable clause reduction (keep learned clauses)
--no-rephase            disable rephasing / resetting of saved phases
--no-restart            disable restarting (otherwise moving average based)
--no-reuse              disable reusing the trail during restart
--no-reusestable        disable trail reuse in stable mode
--no-save               disable phase saving (use default decision phase)
--no-shrink             disable all-uip shrinking of minimized clause
--no-simplification     disable preprocessing and inprocessing
--no-sort-analyzed      disable bumped sorting in focused mode
--no-sort-deduced       disable sorting of deduced in learned clause
--no-stable             disable stable mode and always use focused mode
--no-strengthening      disable self-subsuming resolution
--no-subsumption        disable subsumption during variable elimination
--no-subsumption-limits disable size, occurrence and round limits
--no-target             disable target phases (heuristic in stable mode)
--no-tier1              disable keeping tier 1 clauses (glue <= 2)
--no-tier2              disable delaying reduction of tier 2 (glue <= 6)
--no-true               disable default 'true' decision phase (use 'false')
--no-used               disable keeping used clauses (above tier 1 limit)
--no-variadic           disable literals embedding as in clauses
--no-virtual            disable virtual binary clauses
--no-vivification       disable vivification
--no-vivificationlimits disable limits in vivification
--no-vivifyimply        disable subsumption detection during vivification
--no-vmtf               disable VMTF and always use VSIDS instead
--no-vsids              disable VSIDS and always use VMTF instead
--no-watches            disable clause watches and use counters instead
EOF
