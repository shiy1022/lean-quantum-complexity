import «BQP-program-opcode-reference»
import «BQP-program-zipper-reference»
import «BQP-program-compiler-reference»
import «BQP-program-sweeps-reference»
import «BQP-program-dictionary-reference»
import «BQP-program-transfer-reference»
import «BQP-program-sweep-reference»
import «BQP-program-reversal-reference»
import «BQP-program-adjoint-phase-reference»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
open Lean Elab Command in
run_cmd do
  for name in #[``BQPBridgeReference.opcodeLaws,
    ``BQPBridgeReference.tapeZipper,
    ``BQPBridgeReference.compilerData,
    ``BQPBridgeReference.inputEndpointSweeps,
    ``BQPBridgeReference.blockDictionary,
    ``BQPBridgeReference.basisBlockTransfer,
    ``BQPBridgeReference.gateSweep,
    ``BQPBridgeReference.adjointReversal,
    ``BQPBridgeReference.adjointPhase] do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_PROGRAM_CHECKED {name}; axioms {axs}"
