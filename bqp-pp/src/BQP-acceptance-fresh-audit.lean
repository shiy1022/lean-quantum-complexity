import «BQP-acceptance-pair-counts»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPPaths.reindex_amplitude, ``BQPPaths.forward_amplitude,
    ``BQPPaths.padded_input_amplitude, ``BQPPaths.fiber_norm,
    ``BQPPaths.endpointCount_le, ``BQPPaths.endpoint_coefficient_bound,
    ``BQPPaths.amplitude_pair_count, ``BQPPaths.circuit_acceptance_pair_counts] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_ACCEPTANCE_CHECKED {name}; axioms {axs}"
