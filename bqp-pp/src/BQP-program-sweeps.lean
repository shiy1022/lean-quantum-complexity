import «BQP-program-block-transfer»
import «BQP-program-sweep-reference»
import «BQP-program-sweeps-reference»

set_option autoImplicit false
namespace BQPProgram
open ShiShallow BQPPaths BQPGates

 theorem forward_sweep (C : Checker) {n : ℕ} (gs : List (Instr n)) (z : Bits n)
    (p : ZMod 8) (ct de bd : Bool) (w : List Bool) (hw : hadamardCount gs ≤ w.length) :
    ∃ ct' : Bool, (forwardBody gs).foldl C.step (p, [], List.ofFn z, ct, de, bd, w) =
      (p + phaseRun gs z w, [], List.ofFn (forwardRun gs z w), ct', de, bd,
        w.drop (hadamardCount gs)) := by
  have h := BQPBridgeReference.gateSweep C.step (fun n => @hadamardCount n)
    (fun n => @gateBlock n) (fun n => @forward n) (fun n => @phaseStep n)
    (fun n => @forwardRun n) (fun n => @phaseRun n)
    (fun _ => rfl)
    (by intro n i gs; simp [hadamardCount])
    (by intro n g gs hg; cases g <;> simp_all [hadamardCount])
    (block_transfer C).1 (block_transfer C).2.1
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [forwardRun])
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [phaseRun])
  exact h n gs z p ct de bd w hw

 theorem adjoint_sweep (C : Checker) {n : ℕ} (gs : List (Instr n)) (z : Bits n)
    (p : ZMod 8) (ct de bd : Bool) (w : List Bool) (hw : hadamardCount gs ≤ w.length) :
    ∃ ct' : Bool, (gs.map adjointBlock).flatten.foldl C.step (p, [], List.ofFn z, ct, de, bd, w) =
      (p + adjointPhaseRun gs z w, [], List.ofFn (forwardRun gs z w), ct', de, bd,
        w.drop (hadamardCount gs)) := by
  have h := BQPBridgeReference.gateSweep C.step (fun n => @hadamardCount n)
    (fun n => @adjointBlock n) (fun n => @forward n) (fun n => @adjointPhaseStep n)
    (fun n => @forwardRun n) (fun n => @adjointPhaseRun n)
    (fun _ => rfl)
    (by intro n i gs; simp [hadamardCount])
    (by intro n g gs hg; cases g <;> simp_all [hadamardCount])
    (block_transfer C).2.2.1 (block_transfer C).2.2.2.1
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [forwardRun])
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [adjointPhaseRun])
  exact h n gs z p ct de bd w hw

 theorem input_sweeps (C : Checker) :
    (∀ (l : List Bool) (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
      (load l ++ List.replicate l.length 0).foldl C.step (p, [], [], ct, de, bd, w) =
        (p, [], l, ct, de, bd, w)) ∧
    (∀ (l e : List Bool), l.length = e.length →
      ∀ (p : ZMod 8) (ct de bd : Bool) (w : List Bool),
      (endpoint l ++ List.replicate l.length 0).foldl C.step (p, [], e, ct, de, bd, w) =
        (p, [], e, ct, de || decide (e ≠ l), bd, w)) := by
  have h := BQPBridgeReference.inputEndpointSweeps C.step load endpoint C.step_laws
    rfl (fun _ _ => rfl) rfl (fun _ _ => rfl)
  exact ⟨h.2.2.1, h.2.2.2.2⟩

end BQPProgram
