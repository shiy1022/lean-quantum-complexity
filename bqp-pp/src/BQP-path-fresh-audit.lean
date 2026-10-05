import «BQP-path-correspondence»
import «BQP-path-fiber-sum»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPBridgeReference.reindex, ``BQPBridgeReference.gateData,
    ``BQPBridgeReference.phaseAgreement, ``BQPPaths.forward_backward_correspondence,
    ``BQPPaths.inputState_delta, ``BQPPaths.fiber_sum] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_PATH_CHECKED {name}; axioms {axs}"
