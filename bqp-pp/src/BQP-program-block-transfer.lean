import «BQP-program-data»
import «BQP-canonical-adjoint»
import «BQP-program-dictionary-reference»
import «BQP-program-transfer-reference»
import «BQP-bridge-gate-reference»

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BQPProgram
open ShiShallow BQPPaths BQPGates

/-- Every actual compiler block implements the same state and phase operation
as the canonical quantum path. Both CNOT orientations are included. -/
theorem block_transfer (C : Checker) :
(∀ (m : ℕ) (i : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          ∃ ct' : Bool, (gateBlock (Instr.h i)).foldl C.step (p, [], List.ofFn z, ct, de, bd, w)
            = (p + phaseStep (Instr.h i) w.headI z, [],
                List.ofFn (forward (Instr.h i) w.headI z), ct', de, bd || w.isEmpty,
                w.tail))
      ∧ (∀ (m : ℕ) (g : Instr m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), (∀ i, g ≠ Instr.h i) →
          ∃ ct' : Bool, (gateBlock g).foldl C.step (p, [], List.ofFn z, ct, de, bd, w)
            = (p + phaseStep g false z, [], List.ofFn (forward g false z), ct', de, bd, w))
      -- THE ADJOINT BLOCKS, on basis strings
      ∧ (∀ (m : ℕ) (i : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          ∃ ct' : Bool, (adjointBlock (Instr.h i)).foldl C.step (p, [], List.ofFn z, ct, de, bd, w)
            = (p + adjointPhaseStep (Instr.h i) w.headI z, [],
                List.ofFn (forward (Instr.h i) w.headI z), ct', de, bd || w.isEmpty,
                w.tail))
      ∧ (∀ (m : ℕ) (g : Instr m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool), (∀ i, g ≠ Instr.h i) →
          ∃ ct' : Bool, (adjointBlock g).foldl C.step (p, [], List.ofFn z, ct, de, bd, w)
            = (p + adjointPhaseStep g false z, [], List.ofFn (forward g false z), ct', de, bd, w))
      -- THE OUTPUT-WIRE TEST BLOCK, on basis strings
      ∧ (∀ (m : ℕ) (out : Fin m) (z : Bits m) (p : ZMod 8) (ct de bd : Bool)
          (w : List Bool),
          (List.replicate (out : ℕ) 1 ++ ([8] ++ List.replicate (out : ℕ) 0)).foldl C.step
              (p, [], List.ofFn z, ct, de, bd, w)
            = (p, [], List.ofFn z, ct, de || !(z out), bd, w)) := by
  obtain ⟨hflat, hwrap, hT, hTd, hS, hSd, hX, hH, hE8, hCl, hCg⟩ :=
    BQPBridgeReference.blockDictionary C.step C.step_laws
  obtain ⟨fw, ph, pa, hfwh, hfws, hfwt, hfwx, hfwc,
    hphh, hphs, hpht, hphx, hphc, hpah, hpas, hpat, hpax, hpac,
    hInv, hCoef, hMat, hInv2, hCancel, hWrite, hUndo, hOverwrite,
    hlen, hcell, hset, hD, hDA⟩ := BQPBridgeReference.gateData
  apply BQPBridgeReference.basisBlockTransfer C.step
    (fun n => @gateBlock n) (fun n => @adjointBlock n)
    (fun n => @forward n) (fun n => @phaseStep n) (fun n => @adjointPhaseStep n)
  all_goals first
    | assumption
    | (intros; rfl)
    | (intro m i j hij hlt
       simp [gateBlock, wrap, hlt, Nat.not_lt.mpr (Nat.le_of_lt hlt)])

end BQPProgram
