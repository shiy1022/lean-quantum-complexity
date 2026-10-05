import «BQP-gate-semantics»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000

open Lean Elab Command in
run_cmd do
  for name in #[``BQPGates.omega_sq, ``BQPGates.apply_non_hadamard,
    ``BQPGates.coefficient_is_eighth_root, ``BQPGates.runLayered_flatten,
    ``BQPGates.concrete_path_expansion, ``BQPGates.predecessor_involutive,
    ``BQPGates.predecessor_unique, ``BQPGates.compatible_map_inverts_forward] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_GATE_CHECKED {name}; axioms {axs}"
