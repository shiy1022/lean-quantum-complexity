import ReversibleTickRetreatIterationBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickRetreatIterationTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  descendingProgramTemplate (tickRetreatStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3)

theorem tickRetreatIterationTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickRetreatIterationTemplate tm bound).Embeds :=
  descendingProgramTemplate_embeds _ _ (tickRetreatStepTemplate_embeds tm (bound+1) bound)

theorem tickRetreatIterationTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickRetreatIterationTemplate tm bound).Runs :=
  descendingProgramTemplate_run _ _ (tickRetreatStepTemplate_embeds tm (bound+1) bound)
    (tickRetreatStepTemplate_run tm (bound+1) bound)

theorem tickRetreatIterationTemplate_ready (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstInput firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    (tickRetreatIterationTemplate tm bound).ready cs := by
  let p := tickRetreatStepTemplate tm (bound+1) bound
  let remaining := tickTraversalSpare tm 3
  change descendingTemplateReady p remaining (cs remaining) cs
  refine descendingTemplateReady_of_invariant p remaining
    (fun count (t : CounterCfg _ Unit) => TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput count t.counters)
    ?_ ?_ ?_ (cs remaining) ⟨none,cs,[]⟩ hs
  · intro k t ht
    have hb := TickRetreatIterationBudget.remaining_update tm bound wireBound capacity layers firstInput firstOutput
      (k+1) k t.counters ht (by have hk := ht.2.2.2.2.1; omega)
    exact tickRetreatStepTemplate_ready tm (bound+1) bound wireBound _ hb.1 hb.2.1 hb.2.2.2.1
      (by rw [hb.2.2.1]; exact hc) hsize
  · intro k t _
    rw [tickRetreatStepTemplate_spare_frame tm (bound+1) bound _ 3 (by decide) (by decide) (by decide)]
    simp [remaining]
  · intro k t ht
    exact tickRetreatIterationBudget_next tm bound wireBound capacity layers firstInput firstOutput k t.counters ht hc hsize

end ShiReversibleGenerator
