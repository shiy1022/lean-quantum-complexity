import ReversibleTickForwardIterationBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickForwardIterationTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  descendingProgramTemplate (tickForwardStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3)

theorem tickForwardIterationTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickForwardIterationTemplate tm bound).Embeds :=
  descendingProgramTemplate_embeds _ _ (tickForwardStepTemplate_embeds tm (bound+1) bound)

theorem tickForwardIterationTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickForwardIterationTemplate tm bound).Runs :=
  descendingProgramTemplate_run _ _ (tickForwardStepTemplate_embeds tm (bound+1) bound)
    (tickForwardStepTemplate_run tm (bound+1) bound)

/-- The real runtime tick count and window allowance establish every iteration's readiness. -/
theorem tickForwardIterationTemplate_ready (tm : Turing.FinTM2) (bound wireBound capacity : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickForwardIterationBudget tm bound wireBound capacity (cs (tickTraversalSpare tm 3)) cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    (tickForwardIterationTemplate tm bound).ready cs := by
  let p := tickForwardStepTemplate tm (bound+1) bound
  let remaining := tickTraversalSpare tm 3
  change descendingTemplateReady p remaining (cs remaining) cs
  refine descendingTemplateReady_of_invariant p remaining
    (fun count (t : CounterCfg _ Unit) => TickForwardIterationBudget tm bound wireBound capacity count t.counters)
    ?_ ?_ ?_ (cs remaining) ⟨none,cs,[]⟩ hs
  · intro k t ht
    have hbudget := TickForwardIterationBudget.remaining_update tm bound wireBound capacity (k+1) k t.counters ht (by have hk := ht.2.2.2.2.1; omega)
    apply tickForwardStepTemplate_ready tm (bound+1) bound wireBound _ hbudget.1 hbudget.2.1 hbudget.2.2.2.1
    · rw [hbudget.2.2.1]; exact hc
    · exact hsize
  · intro k t _
    rw [tickForwardStepTemplate_spare_frame tm (bound+1) bound _ 3 (by decide) (by decide)]
    simp [remaining]
  · intro k t ht
    exact tickForwardIterationBudget_next tm bound wireBound capacity k t.counters ht hc hsize

end ShiReversibleGenerator
