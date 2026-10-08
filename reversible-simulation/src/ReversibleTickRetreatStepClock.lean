import ReversibleTickRetreatStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- One actual emission-and-retreat step has a polynomial instruction clock from concrete budgets. -/
theorem tickRetreatStepTemplate_clock (tm : Turing.FinTM2) (inputStride bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      cs (.inl 1)=capacity.eval n → fixedGuardedEmitterReady (tickTraversalSupply tm) cs →
      CounterBudget cs (.inl 9) (budget.eval n) → TickWindowBudget tm inputStride bound (budget.eval n) cs →
      0 < cs (.inl 1) → cs (.inl 9) ≤ layers.eval n →
      (tickRetreatStepTemplate tm inputStride bound).steps cs ≤ clock.eval n := by
  let nextLayers := layers+(Polynomial.C (tickWidthSlope tm)*capacity+Polynomial.C (tickWidthOffset tm))*
    Polynomial.C (37*tickSizeBound tm+1)
  obtain ⟨forestClock,hforest⟩ := tickForestTemplate_clock tm inputStride bound false capacity budget layers hsize
  obtain ⟨advanceClock,hadvance⟩ := tickWindowRetreatTemplate_polynomial tm bound (budget+nextLayers)
  refine ⟨forestClock+advanceClock,?_⟩
  intro n cs hcap hr hb hw hc hl
  let after := (tickForestTemplate tm inputStride bound false).counters cs
  have hs := tickForestTemplate_ready_and_budget tm inputStride bound false (budget.eval n) cs hr hb hw hc hsize
  have hcount : after (.inl 9) ≤ nextLayers.eval n := by
    calc
      _ = cs (.inl 9)+tickForestLayerCount tm (cs (.inl 1)) := tickForestTemplate_count tm inputStride bound false cs
      _ ≤ layers.eval n+configurationWidth tm (cs (.inl 1))*(37*tickSizeBound tm+1) :=
        Nat.add_le_add hl (tickForestLayerCount_bound tm _ hc)
      _ = _ := by rw [tickWidth_affine,hcap]; simp only [nextLayers,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  have hab : ∀ q,after q ≤ (budget+nextLayers).eval n := by
    intro q
    rw [Polynomial.eval_add]
    by_cases hq : q=Sum.inl 9
    · subst q; exact hcount.trans (Nat.le_add_left _ _)
    · exact (hs.2.1 q hq).trans (Nat.le_add_right _ _)
  have ha := hadvance n after hab ((tickWindowRetreatTemplate_ready tm bound after).mpr hs.2.2.2.2.2.1)
  have hf := hforest n cs hcap hr hb hw hc hl
  change (tickForestTemplate tm inputStride bound false).steps cs+(tickWindowRetreatTemplate tm bound).steps after ≤ _
  simpa only [Polynomial.eval_add] using Nat.add_le_add hf ha

end ShiReversibleGenerator
