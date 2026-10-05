import «BQP-canonical-paths»
import «BQP-program-reversal-reference»

set_option autoImplicit false
namespace BQPPaths
open ShiShallow BQPGates

/-- Instantiate the proved program reversal laws at the explicit circuit
recursions. Every recurrence and gate inverse is discharged here. -/
theorem canonical_reversal :
    (∀ (n : ℕ) (as bs : List (Instr n)) (z : Bits n) (w : List Bool),
      forwardRun (as ++ bs) z w = forwardRun bs (forwardRun as z w)
        (w.drop (hadamardCount as))) ∧
    (∀ (n : ℕ) (as bs : List (Instr n)) (z : Bits n) (w : List Bool),
      backwardWitness (as ++ bs) z w = backwardWitness as z w ++
        backwardWitness bs (forwardRun as z w) (w.drop (hadamardCount as))) ∧
    (∀ (n : ℕ) (gs : List (Instr n)) (z : Bits n) (w u : List Bool),
      w.length = hadamardCount gs →
        forwardRun gs z (w ++ u) = forwardRun gs z w ∧
          backwardWitness gs z (w ++ u) = backwardWitness gs z w) ∧
    (∀ (n : ℕ) (gs : List (Instr n)) (z : Bits n) (w : List Bool),
      w.length = hadamardCount gs →
        forwardRun gs.reverse (forwardRun gs z w) (backwardWitness gs z w).reverse = z ∧
          backwardWitness gs.reverse (forwardRun gs z w) (backwardWitness gs z w).reverse =
            w.reverse) := by
  have h := BQPBridgeReference.adjointReversal
    (fun n => @hadamardCount n) (fun n => @forward n)
    (fun n => @forwardRun n) (fun n => @backwardWitness n)
    (fun _ => rfl)
    (by intro n i gs; simp [hadamardCount])
    (by intro n g gs hg; cases g <;> simp_all [hadamardCount])
    (fun _ _ _ _ => rfl)
    (by
      intro n g hg a z
      rw [forward_non_hadamard g hg, forward_non_hadamard g hg]
      exact predecessor_involutive g z)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [forwardRun])
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by intro n g gs z w hg; cases g <;> simp_all [backwardWitness])
    (fun _ gs z w => backwardWitness_length gs z w)
  exact h.2.2

end BQPPaths
