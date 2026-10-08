import ReversibleTickInverseAdvanceBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Remaining-tick allowance is consumed by exactly one actual emission-and-advance step. -/
theorem tickInverseAdvanceIterationBudget_next (tm : Turing.FinTM2) (bound wireBound capacity k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickForwardIterationBudget tm bound wireBound capacity (k+1) cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    TickForwardIterationBudget tm bound wireBound capacity k
      ((tickInverseAdvanceStepTemplate tm (bound+1) bound).counters (Function.update cs (tickTraversalSpare tm 3) k)) := by
  let initial := Function.update cs (tickTraversalSpare tm 3) k
  have ht : TickForwardIterationBudget tm bound wireBound capacity (k+1) initial := TickForwardIterationBudget.remaining_update tm bound wireBound capacity (k+1) k cs hs (by have hk := hs.2.2.2.2.1; omega)
  have hpos : 0 < initial (.inl 1) := by rw [ht.2.2.1]; exact hc
  have hcap := tickInverseAdvanceStepTemplate_control_frame tm (bound+1) bound initial 1 (by decide) (by decide) (by decide)
  have hallow : initial (tickTraversalSpare tm 2)+2*(configurationWidth tm (initial (.inl 1))*(bound+1)) ≤ wireBound := by
    have hf := ht.2.2.2.2.2
    rw [ht.2.2.1]
    have hm := Nat.mul_le_mul_right (configurationWidth tm capacity*(bound+1)) (by omega : 2 ≤ k+1+1)
    omega
  refine ⟨tickInverseAdvanceStepTemplate_ready_preserved tm (bound+1) bound initial ht.1,
    tickInverseAdvanceStepTemplate_static_budget tm (bound+1) bound wireBound initial ht.1 ht.2.1 ht.2.2.2.1 hpos hsize,
    hcap.trans ht.2.2.1,tickInverseAdvanceStepTemplate_windows tm bound wireBound initial hallow,?_,?_⟩
  · have hk := ht.2.2.2.2.1; omega
  · rw [tickInverseAdvanceStepTemplate_output]
    change initial (tickTraversalSpare tm 2)+configurationWidth tm (initial (.inl 1))*(bound+1)+
      (k+1)*(configurationWidth tm capacity*(bound+1)) ≤ wireBound
    rw [ht.2.2.1]
    have hf := ht.2.2.2.2.2
    simp only [Nat.add_mul,Nat.one_mul] at hf ⊢
    omega

end ShiReversibleGenerator
