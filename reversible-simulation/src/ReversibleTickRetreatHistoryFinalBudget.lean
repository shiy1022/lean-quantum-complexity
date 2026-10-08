import ReversibleTickRetreatHistoryReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- After the actual loop, both pointers are exactly at the retained boundary slice. -/
theorem tickRetreatHistoryTemplate_final_budget (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput 0
      ((tickRetreatIterationTemplate tm bound).counters cs) := by
  let p := tickRetreatStepTemplate tm (bound+1) bound
  let remaining := tickTraversalSpare tm 3
  have h : ∀ k t,TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput k t →
      TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput 0
        (descendingTemplateCounters p remaining k t) := by
    intro k
    induction k with
    | zero => intro t ht; exact ht
    | succ k ih =>
      intro t ht
      exact ih _ (tickRetreatHistoryBudget_next tm bound wireBound capacity layers firstOutput k t ht hc hsize)
  change TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput 0
    (Function.update (descendingTemplateCounters p remaining (cs remaining) cs) remaining 0)
  exact TickRetreatHistoryBudget.remaining_update tm bound wireBound capacity layers firstOutput 0 0 _
    (h _ cs hs) (Nat.zero_le _)

theorem tickRetreatHistoryTemplate_boundary_pointers (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    let final := (tickRetreatIterationTemplate tm bound).counters cs
    final (.inl 0)=(firstOutput+bound)-configurationWidth tm capacity*(bound+1) ∧ final (tickTraversalSpare tm 2)=firstOutput ∧ final (tickTraversalSpare tm 3)=0 := by
  have hf := tickRetreatHistoryTemplate_final_budget tm bound wireBound capacity layers firstOutput cs hs hc hsize
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.zero_mul,Nat.add_zero] using hf.2.2.2.2.2.1
  · simpa only [Nat.zero_mul,Nat.add_zero] using hf.2.2.2.2.2.2.1
  · change Function.update _ (tickTraversalSpare tm 3) 0 (tickTraversalSpare tm 3)=0
    exact Function.update_self _ _ _

end ShiReversibleGenerator
