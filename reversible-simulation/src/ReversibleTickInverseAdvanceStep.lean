import ReversibleTickRetreatStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Emit inverse forest blocks while advancing time slices, so prepending reverses slice order. -/
noncomputable def tickInverseAdvanceStepTemplate (tm : Turing.FinTM2) (inputStride bound : Nat) :=
  sequenceProgramTemplate (tickForestTemplate tm inputStride bound true) (tickWindowAdvanceTemplate tm bound)

theorem tickInverseAdvanceStepTemplate_embeds (tm : Turing.FinTM2) (inputStride bound : Nat) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickForestTemplate_embeds tm inputStride bound true)
    (tickWindowAdvanceTemplate_embeds tm bound)

theorem tickInverseAdvanceStepTemplate_run (tm : Turing.FinTM2) (inputStride bound : Nat) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).Runs :=
  sequenceProgramTemplate_run _ _ (tickForestTemplate_embeds tm inputStride bound true)
    (tickForestTemplate_run tm inputStride bound true) (tickWindowAdvanceTemplate_run tm bound)

theorem tickInverseAdvanceStepTemplate_ready (tm : Turing.FinTM2) (inputStride bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride bound wireBound cs)
    (hc : 0 < cs (.inl 1)) (hsize : tickSizeBound tm ≤ bound) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).ready cs := by
  have hs := tickForestTemplate_ready_and_budget tm inputStride bound true wireBound cs hr hb hw hc hsize
  exact ⟨hs.1,(tickWindowAdvanceTemplate_ready tm bound _).mpr hs.2.2.2.2.2.1⟩

theorem tickInverseAdvanceStepTemplate_bytes (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).bytes cs=(tickForestTemplate tm inputStride bound true).bytes cs := rfl

end ShiReversibleGenerator
