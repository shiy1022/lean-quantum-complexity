import «BQP-canonical-reversal»
import «BQP-program-adjoint-phase-reference»

set_option autoImplicit false
namespace BQPPaths
open ShiShallow BQPGates

def adjointPhaseStep {n : ℕ} (g : Instr n) (a : Bool) (z : Bits n) : ZMod 8 :=
  match g with
  | .h i => if z i && a then 4 else 0
  | .s i => if z i then 6 else 0
  | .t i => if z i then 7 else 0
  | _ => 0

def adjointPhaseRun {n : ℕ} : List (Instr n) → Bits n → List Bool → ZMod 8
  | [], _, _ => 0
  | .h i :: gs, z, w =>
      adjointPhaseStep (.h i) w.headI z + adjointPhaseRun gs (forward (.h i) w.headI z) w.tail
  | g :: gs, z, w => adjointPhaseStep g false z + adjointPhaseRun gs (forward g false z) w

 theorem nonHadamard_phase_cancel {n : ℕ} (g : Instr n) (hg : ∀ i, g ≠ Instr.h i)
    (a : Bool) (z : Bits n) :
    phaseStep g a z + adjointPhaseStep g a (forward g a z) = 0 := by
  cases g with
  | h i => exact False.elim (hg i rfl)
  | s i => cases hz : z i <;> norm_num [phaseStep, adjointPhaseStep, forward, predecessor, hz] <;> decide
  | t i => cases hz : z i <;> norm_num [phaseStep, adjointPhaseStep, forward, predecessor, hz] <;> decide
  | x i => simp [phaseStep, adjointPhaseStep]
  | cnot i j hij => simp [phaseStep, adjointPhaseStep]

/-- The concrete adjoint phase fold pays exactly the negative of the forward
phase on the reversed destroyed-bit witness. No phase agreement is assumed. -/
theorem canonical_adjoint_phase {n : ℕ} (gs : List (Instr n)) (z : Bits n)
    (w : List Bool) (hw : w.length = hadamardCount gs) :
    adjointPhaseRun gs.reverse (forwardRun gs z w) (backwardWitness gs z w).reverse +
      phaseRun gs z w = 0 := by
  have h := BQPBridgeReference.adjointPhase
    (fun n => @hadamardCount n) (fun n => @forward n)
    (fun n => @phaseStep n) (fun n => @adjointPhaseStep n)
    (fun n => @forwardRun n) (fun n => @backwardWitness n)
    (fun n => @phaseRun n) (fun n => @adjointPhaseRun n)
    (fun _ => rfl)
    (by intro n i gs; simp [hadamardCount])
    (by intro n g gs hg; cases g <;> simp_all [hadamardCount])
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ g hg a z => nonHadamard_phase_cancel g hg a z)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [forwardRun])
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [backwardWitness])
    (fun _ gs z w => backwardWitness_length gs z w)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [phaseRun])
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [adjointPhaseRun])
    (by intro n gs; simp [hadamardCount])
    canonical_reversal.1 canonical_reversal.2.2.1 canonical_reversal.2.2.2
  exact h.2.2 n gs z w hw

end BQPPaths
