import ReversibleTickWindowRetreat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Emit a forward forest while traversing time slices from last to first. -/
noncomputable def tickRetreatStepTemplate (tm : Turing.FinTM2) (inputStride bound : Nat) :=
  sequenceProgramTemplate (tickForestTemplate tm inputStride bound false) (tickWindowRetreatTemplate tm bound)

theorem tickRetreatStepTemplate_embeds (tm : Turing.FinTM2) (inputStride bound : Nat) :
    (tickRetreatStepTemplate tm inputStride bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickForestTemplate_embeds tm inputStride bound false)
    (tickWindowRetreatTemplate_embeds tm bound)

theorem tickRetreatStepTemplate_run (tm : Turing.FinTM2) (inputStride bound : Nat) :
    (tickRetreatStepTemplate tm inputStride bound).Runs :=
  sequenceProgramTemplate_run _ _ (tickForestTemplate_embeds tm inputStride bound false)
    (tickForestTemplate_run tm inputStride bound false) (tickWindowRetreatTemplate_run tm bound)

theorem tickRetreatStepTemplate_ready (tm : Turing.FinTM2) (inputStride bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride bound wireBound cs)
    (hc : 0 < cs (.inl 1)) (hsize : tickSizeBound tm ≤ bound) :
    (tickRetreatStepTemplate tm inputStride bound).ready cs := by
  have hs := tickForestTemplate_ready_and_budget tm inputStride bound false wireBound cs hr hb hw hc hsize
  exact ⟨hs.1,(tickWindowRetreatTemplate_ready tm bound _).mpr hs.2.2.2.2.2.1⟩

theorem tickRetreatStepTemplate_bytes (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickRetreatStepTemplate tm inputStride bound).bytes cs=(tickForestTemplate tm inputStride bound false).bytes cs := by
  change (tickWindowRetreatTemplate tm bound).bytes _++_=_
  rw [tickWindowRetreatTemplate_bytes]
  rfl

end ShiReversibleGenerator
