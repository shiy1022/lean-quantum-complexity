import «BQP-canonical-amplitude»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPPaths.backwardWitness_length, ``BQPPaths.forwardRun_unique,
    ``BQPPaths.phaseRun_unique, ``BQPPaths.canonical_amplitude,
    ``BQPPaths.canonical_acceptance] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_CANONICAL_CHECKED {name}; axioms {axs}"
