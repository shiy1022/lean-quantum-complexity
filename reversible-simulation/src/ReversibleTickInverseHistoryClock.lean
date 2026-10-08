import ReversibleTickInverseHistoryReady
import ReversibleTickInverseAdvanceIterationClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Polynomial clock for the real count setup, stride18 boundary tick, and regular inverse loop. -/
theorem tickInverseHistoryTemplate_clock (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      fixedGuardedEmitterReady (tickTraversalSupply tm) cs → CounterBudget cs (.inl 9) (budget.eval n) →
      TickWindowBudget tm 18 bound (budget.eval n) cs → cs (.inl 1)=capacity.eval n →
      0 < capacity.eval n → 0 < cs (tickTraversalSpare tm 7) →
      cs (.inl 9)+cs (tickTraversalSpare tm 7)*tickForestLayerCount tm (capacity.eval n) ≤ layers.eval n →
      cs (tickTraversalSpare tm 2)+(cs (tickTraversalSpare tm 7)+1)*
        (configurationWidth tm (capacity.eval n)*(bound+1)) ≤ budget.eval n →
      (tickInverseHistoryTemplate tm bound).steps cs ≤ clock.eval n := by
  obtain ⟨copyClock,hcopy⟩ := tickHistoryCountTemplate_polynomial tm (budget+layers)
  obtain ⟨boundaryClock,hboundary⟩ := tickInverseAdvanceStepTemplate_clock tm 18 bound capacity budget layers hsize
  obtain ⟨loopClock,hloop⟩ := tickInverseAdvanceIterationTemplate_clock tm bound capacity budget layers hsize
  refine ⟨copyClock+(boundaryClock+loopClock),?_⟩
  intro n cs hr hb hw hcap hc ht hl hf
  let initial := (tickHistoryCountTemplate tm).counters cs
  let after := (tickInverseAdvanceStepTemplate tm 18 bound).counters initial
  have hinitial : initial=Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1) := tickHistoryCountTemplate_counters tm cs
  have hir : fixedGuardedEmitterReady (tickTraversalSupply tm) initial := by
    rw [hinitial]; simpa [fixedGuardedEmitterReady,tickTraversalSpare] using hr
  have hib : CounterBudget initial (.inl 9) (budget.eval n) := by
    rw [hinitial]; exact hb.update _ _ ((Nat.sub_le _ _).trans (hb _ (by simp [tickTraversalSpare])))
  have hiw : TickWindowBudget tm 18 bound (budget.eval n) initial := by
    rw [hinitial]; simpa [TickWindowBudget,tickTraversalSpare] using hw
  have hic : initial (.inl 1)=capacity.eval n := by rw [hinitial]; simpa [tickTraversalSpare] using hcap
  have hi9 : initial (.inl 9)=cs (.inl 9) := by rw [hinitial]; simp [tickTraversalSpare]
  have hcount : cs (.inl 9) ≤ layers.eval n := by omega
  have hall : ∀ q,cs q ≤ (budget+layers).eval n := by
    intro q
    rw [Polynomial.eval_add]
    by_cases hq : q=Sum.inl 9
    · subst q; exact hcount.trans (Nat.le_add_left _ _)
    · exact (hb q hq).trans (Nat.le_add_right _ _)
  have hcp := hcopy n cs hall hr.2.2.1
  have hbc := hboundary n initial hic hir hib hiw (by rw [hic]; exact hc) (by rw [hi9]; exact hcount)
  have ha := tickInverseHistoryBoundary_budget tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    cs hr hb hw hcap hc hsize ht hl hf
  have hlc := hloop n after ha hc
  change (tickHistoryCountTemplate tm).steps cs+((tickInverseAdvanceStepTemplate tm 18 bound).steps initial+
    (tickInverseAdvanceIterationTemplate tm bound).steps after) ≤ _
  simpa only [Polynomial.eval_add] using Nat.add_le_add hcp (Nat.add_le_add hbc hlc)

end ShiReversibleGenerator
