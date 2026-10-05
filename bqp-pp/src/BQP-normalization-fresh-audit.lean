import «BQP-counting-normalization»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPCounting.count_prefix, ``BQPCounting.count_pairedPrefix,
    ``BQPCounting.count_pairedPrefix_double, ``BQPCounting.pairedPrefix_representation] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_NORMALIZATION_CHECKED {name}; axioms {axs}"
