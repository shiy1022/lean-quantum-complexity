import ReversibleStridedBindingSequenceContinuation
import ReversibleCoordinateBindingBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

theorem stridedTickCoordinateAddress_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (inputStride : Nat) (coordinate : TickSymbolicCoordinate tm) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      stridedTickCoordinateAddress tm env inputStride coordinate cs ≤ budget.eval n := by
  obtain ⟨budget, hb⟩ := tickCoordinateAddress_polynomial tm env coordinate bound
  refine ⟨bound + Polynomial.C inputStride * budget, ?_⟩
  intro n cs hc
  have hn : naturalConfigurationAddress tm (cs env.capacity)
      (tickSymbolicCoordinateEval (cs env.capacity) (cs env.position) coordinate) ≤ budget.eval n :=
    (Nat.le_add_left _ (cs env.input)).trans (hb n cs hc)
  simpa only [stridedTickCoordinateAddress, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add (hc env.input) (Nat.mul_le_mul_left inputStride hn)

/-- Finite binding sequences preserve a polynomial bound on every counter and have a polynomial exact clock. -/
theorem stridedCoordinateBindingSequence_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      (∀ q, stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs q ≤ budget.eval n) ∧
      stridedCoordinateBindingSequenceSteps tm env inputStride tasks cs ≤ clock.eval n := by
  induction tasks generalizing bound with
  | nil =>
    refine ⟨bound, 0, ?_⟩
    intro n cs hb
    exact ⟨hb, by simp [stridedCoordinateBindingSequenceSteps]⟩
  | cons task tasks ih =>
    have hvalid := hv task (by simp)
    obtain ⟨addressBudget, ha⟩ := stridedTickCoordinateAddress_polynomial tm (env.withTarget task.2) inputStride task.1 bound
    obtain ⟨firstClock, hc⟩ := stridedTickCoordinateBindingSteps_polynomial tm (env.withTarget task.2) inputStride task.1 hvalid bound
    obtain ⟨budget, clock, htail⟩ := ih (fun t ht => hv t (by simp [ht])) (bound + addressBudget)
    refine ⟨budget, firstClock + clock, ?_⟩
    intro n cs hb
    let after := Function.update cs task.2 (stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs)
    have hb' : ∀ q, after q ≤ (bound + addressBudget).eval n := by
      intro q
      by_cases hq : q = task.2
      · subst q
        simp only [after, Function.update_self, Polynomial.eval_add]
        exact (ha n cs hb).trans (Nat.le_add_left _ _)
      · simp only [after, Function.update_of_ne hq, Polynomial.eval_add]
        exact (hb q).trans (Nat.le_add_right _ _)
    obtain ⟨hf, ht⟩ := htail n after hb'
    refine ⟨hf, ?_⟩
    simpa only [stridedCoordinateBindingSequenceSteps, Polynomial.eval_add, after] using
      Nat.add_le_add (hc n cs hb) ht

end ShiReversibleGenerator
