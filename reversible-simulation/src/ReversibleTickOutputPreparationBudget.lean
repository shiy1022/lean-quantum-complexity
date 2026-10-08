import ReversibleTickOutputPreparation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickPreparedOutputBudget (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (strideBound : Nat) (bound : Polynomial Nat) : Polynomial Nat :=
  let v := tickOutputAddressParameters tm kind strideBound
  Polynomial.C (1 + v.2.1 * v.2.2 + v.2.2) * bound + Polynomial.C v.1

theorem tickPreparedOutputAddress_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (strideBound : Nat) (bound : Polynomial Nat) (n : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hb : ∀ q, cs q ≤ bound.eval n) :
    tickPreparedOutputAddress tm kind strideBound cs ≤ (tickPreparedOutputBudget tm kind strideBound bound).eval n := by
  have hs := hb (tickTraversalSpare tm 2)
  have hc := hb (.inl 1)
  have hp := hb (.inl 2)
  have hm := Nat.mul_le_mul_left ((tickOutputAddressParameters tm kind strideBound).2.1 *
    (tickOutputAddressParameters tm kind strideBound).2.2) hc
  have hn := Nat.mul_le_mul_left (tickOutputAddressParameters tm kind strideBound).2.2 hp
  simp only [tickPreparedOutputAddress, symbolicCellAddress, TickIndexExpr.eval,
    tickPreparedOutputBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  nlinarith

theorem tickOutputPreparationCounters_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (strideBound : Nat) (bound : Polynomial Nat) (n : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hb : ∀ q, cs q ≤ bound.eval n) :
    ∀ q, tickOutputPreparationCounters tm kind strideBound cs q ≤
      (bound + tickPreparedOutputBudget tm kind strideBound bound + Polynomial.C strideBound).eval n := by
  have ha := tickPreparedOutputAddress_bound tm kind strideBound bound n cs hb
  intro q
  by_cases h13 : q = .inl 13
  · subst q
    simp only [tickOutputPreparationCounters, Function.update_self, Polynomial.eval_add, Polynomial.eval_C]
    omega
  · by_cases h12 : q = .inl 12
    · subst q
      simp only [tickOutputPreparationCounters, Function.update_of_ne h13, Function.update_self,
        Polynomial.eval_add, Polynomial.eval_C]
      omega
    · simp only [tickOutputPreparationCounters, Function.update_of_ne h13, Function.update_of_ne h12,
        Polynomial.eval_add, Polynomial.eval_C]
      have h := hb q
      omega

theorem tickOutputPreparationSteps_polynomial (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (strideBound : Nat) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ q, cs q ≤ bound.eval n) → tickOutputPreparationSteps tm kind strideBound cs ≤ clock.eval n := by
  let v := tickOutputAddressParameters tm kind strideBound
  obtain ⟨first, hf⟩ := symbolicCellBindingSteps_polynomial .position (tickTraversalSpare tm 2)
    (.inl 1) (.inl 2) (.inl 3) (.inl 12) v.1 v.2.1 v.2.2
    (by simp [tickTraversalSpare]) (by simp) (by simp [tickTraversalSpare]) (by simp) (by simp) bound
  refine ⟨first + Polynomial.C 2 * bound + Polynomial.C 7 * tickPreparedOutputBudget tm kind strideBound bound +
    Polynomial.C (3 + strideBound), ?_⟩
  intro n cs hb
  have hfirst := hf n cs hb
  have ha := tickPreparedOutputAddress_bound tm kind strideBound bound n cs hb
  have h13 := hb (.inl 13)
  simp only [tickOutputPreparationSteps, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  dsimp only [v] at hfirst
  omega

theorem tickOutputPreparation_ready_preserved (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (h : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) (tickOutputPreparationCounters tm kind bound cs) := by
  simpa [fixedGuardedEmitterReady, tickOutputPreparationCounters] using h

noncomputable def tickOutputPreparationTemplate (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) :
    CounterProgramTemplate (FixedLeafRegister (tickTraversalSupply tm)) where
  Labels := TickOutputPreparationLabels tm kind bound
  finite := fun L f => by letI := f; infer_instance
  code := tickOutputPreparationCode tm kind bound
  entry := fun {L} _ => tickOutputPreparationEntry tm kind bound L
  exit := tickOutputPreparationExit tm kind bound
  ready := fun cs => cs (.inl 3) = 0 ∧ cs (.inl 5) = 0
  steps := tickOutputPreparationSteps tm kind bound
  counters := tickOutputPreparationCounters tm kind bound
  bytes := fun _ => []

theorem tickOutputPreparationTemplate_embeds (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) :
    (tickOutputPreparationTemplate tm kind bound).Embeds := by
  intro L caller stop l
  exact tickOutputPreparationCode_embed tm kind bound caller stop l

theorem tickOutputPreparationTemplate_run (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) :
    (tickOutputPreparationTemplate tm kind bound).Runs := by
  intro L caller stop cs ys hr
  change cs (.inl 3) = 0 ∧ cs (.inl 5) = 0 at hr
  simpa only [tickOutputPreparationTemplate, List.nil_append] using
    tickOutputPreparationCode_run tm kind bound caller stop cs hr.1 hr.2 ys

end ShiReversibleGenerator
