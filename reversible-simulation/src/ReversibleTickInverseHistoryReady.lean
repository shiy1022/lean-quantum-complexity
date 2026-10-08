import ReversibleTickInverseHistoryBoundaryBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Concrete runtime budgets prove readiness of the actual boundary-plus-regular inverse history program. -/
theorem tickInverseHistoryTemplate_ready (tm : Turing.FinTM2) (bound wireBound capacity layers : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm 18 bound wireBound cs)
    (hcap : cs (.inl 1)=capacity) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    (ht : 0 < cs (tickTraversalSpare tm 7))
    (hl : cs (.inl 9)+cs (tickTraversalSpare tm 7)*tickForestLayerCount tm capacity ≤ layers)
    (hf : cs (tickTraversalSpare tm 2)+(cs (tickTraversalSpare tm 7)+1)*
      (configurationWidth tm capacity*(bound+1)) ≤ wireBound) :
    (tickInverseHistoryTemplate tm bound).ready cs := by
  let initial := (tickHistoryCountTemplate tm).counters cs
  let after := (tickInverseAdvanceStepTemplate tm 18 bound).counters initial
  change cs (.inl 5)=0 ∧ ((tickInverseAdvanceStepTemplate tm 18 bound).ready initial ∧
    (tickInverseAdvanceIterationTemplate tm bound).ready after)
  refine ⟨hr.2.2.1,?_,?_⟩
  · have hinitial : initial=Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1) :=
      tickHistoryCountTemplate_counters tm cs
    have hir : fixedGuardedEmitterReady (tickTraversalSupply tm) initial := by
      rw [hinitial]; simpa [fixedGuardedEmitterReady,tickTraversalSpare] using hr
    have hib : CounterBudget initial (.inl 9) wireBound := by
      rw [hinitial]
      exact hb.update _ _ ((Nat.sub_le _ _).trans (hb _ (by simp [tickTraversalSpare])))
    have hiw : TickWindowBudget tm 18 bound wireBound initial := by
      rw [hinitial]; simpa [TickWindowBudget,tickTraversalSpare] using hw
    have hic : initial (.inl 1)=capacity := by rw [hinitial]; simpa [tickTraversalSpare] using hcap
    exact tickInverseAdvanceStepTemplate_ready tm 18 bound wireBound initial hir hib hiw (by rw [hic]; exact hc) hsize
  · have ha := tickInverseHistoryBoundary_budget tm bound wireBound capacity layers cs hr hb hw hcap hc hsize ht hl hf
    exact tickInverseAdvanceIterationTemplate_ready tm bound wireBound capacity after ha.1 hc hsize

end ShiReversibleGenerator
