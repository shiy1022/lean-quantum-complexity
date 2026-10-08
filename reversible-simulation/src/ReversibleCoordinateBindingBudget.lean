import ReversibleLeafFormulaPrinter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
variable {R : Type} [DecidableEq R]

/-- Every fixed symbolic address is polynomially bounded by its source-counter budget. -/
theorem tickCoordinateAddress_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      tickCoordinateAddress tm env coordinate cs ≤ budget.eval n := by
  cases coordinate with
  | inl z =>
    refine ⟨bound + Polynomial.C (tickCoordinateOffset tm (.inl z)), ?_⟩
    intro n cs hb
    have h := hb env.input
    cases z with
    | inl l =>
      simpa [tickCoordinateAddress, tickCoordinateOffset, naturalConfigurationAddress,
        tickSymbolicCoordinateEval] using Nat.add_le_add_right h (((Fintype.equivFin (Option tm.Λ)) l).val)
    | inr v =>
      simpa [tickCoordinateAddress, tickCoordinateOffset, naturalConfigurationAddress,
        tickSymbolicCoordinateEval] using Nat.add_le_add_right h
        (Fintype.card (Option tm.Λ) + ((Fintype.equivFin tm.σ) v).val)
  | inr z =>
    let rank := ((Fintype.equivFin tm.K) z.1.1).val
    let stride := Fintype.card (Option (MachineSymbol tm))
    refine ⟨bound + Polynomial.C (tickCoordinateOffset tm (.inr z)) +
      Polynomial.C (rank * stride) * bound +
      Polynomial.C stride * (Polynomial.C 2 * bound + Polynomial.C z.1.2.allowance), ?_⟩
    intro n cs hb
    have hi := hb env.input
    have hc := hb env.capacity
    have hp := hb env.position
    have he : z.1.2.eval (cs env.capacity) (cs env.position) ≤ 2 * bound.eval n + z.1.2.allowance := by
      have h := z.1.2.eval_bound (cs env.capacity) (cs env.position)
      omega
    have hm := Nat.mul_le_mul_left (rank * stride) hc
    have hn := Nat.mul_le_mul_left stride he
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    simp only [tickCoordinateAddress, tickCoordinateOffset, naturalConfigurationAddress,
      tickSymbolicCoordinateEval]
    dsimp [rank, stride] at hm hn
    nlinarith

/-- Finite binding sequences preserve a polynomial bound on every counter and have a polynomial exact clock. -/
theorem coordinateBindingSequence_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      (∀ q, coordinateBindingSequenceCounters tm env tasks cs q ≤ budget.eval n) ∧
      coordinateBindingSequenceSteps tm env tasks cs ≤ clock.eval n := by
  induction tasks generalizing bound with
  | nil =>
    refine ⟨bound, 0, ?_⟩
    intro n cs hb
    exact ⟨hb, by simp [coordinateBindingSequenceSteps]⟩
  | cons task tasks ih =>
    have hvalid := hv task (by simp)
    obtain ⟨addressBudget, ha⟩ := tickCoordinateAddress_polynomial tm (env.withTarget task.2) task.1 bound
    obtain ⟨firstClock, hc⟩ := tickCoordinateBindingSteps_polynomial tm (env.withTarget task.2) task.1 hvalid bound
    obtain ⟨budget, clock, htail⟩ := ih (fun t ht => hv t (by simp [ht])) (bound + addressBudget)
    refine ⟨budget, firstClock + clock, ?_⟩
    intro n cs hb
    let after := Function.update cs task.2 (tickCoordinateAddress tm (env.withTarget task.2) task.1 cs)
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
    simpa only [coordinateBindingSequenceSteps, Polynomial.eval_add, after] using
      Nat.add_le_add (hc n cs hb) ht

end ShiReversibleGenerator
