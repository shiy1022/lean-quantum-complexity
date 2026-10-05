import «BQP-normalized-threshold»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPCounting.normalized_long_majority, ``BQPCounting.family_shifted_budget] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_NORMALIZED_THRESHOLD_CHECKED {name}; axioms {axs}"
