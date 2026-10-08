import ReversibleExtractionResourceSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionResourceSetupTemplate_ready (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionMasterRegister → Nat) : (extractionResourceSetupTemplate tm backward).ready cs := by
  have hr : ∀ t : ExtractionMasterRegister → Nat,
      (counterPairRetreatTemplate (.inr 11) (.inr 25) (.inr 8)).ready t :=
    fun t => counterPairRetreatTemplate_ready _ _ _ (by decide) (by decide) t
  have hc : ∀ t : ExtractionMasterRegister → Nat,
      (counterPairRetreatTemplate (.inr 11) (.inr 25) (.inr 8)).counters t=
        Function.update (Function.update (Function.update t (.inr 11) (t (.inr 11)-t (.inr 8)))
          (.inr 25) (t (.inr 25)-t (.inr 8))) (.inr 8) 0 :=
    fun t => counterPairRetreatTemplate_counters _ _ _ (by decide) (by decide) (by decide) t
  cases backward <;> simp [extractionResourceSetupTemplate,extractionResourceSetupPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,counterAffineCopyProgramTemplate,
    decrementProgramTemplate,counterAffineAccumulationProgramTemplate,AffineAtom.apply,cleanupCounters_apply,hr,hc]

theorem extractionResourceSetupTemplate_bytes (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionMasterRegister → Nat) : (extractionResourceSetupTemplate tm backward).bytes cs=[] := by
  cases backward <;> simp [extractionResourceSetupTemplate,extractionResourceSetupPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,counterAffineCopyProgramTemplate,
    decrementProgramTemplate,counterAffineAccumulationProgramTemplate,counterPairRetreatTemplate_bytes]

/-- Every forest coordinate is computed from the actual resource endpoint by a finite setup graph. -/
theorem extractionResourceSetupTemplate_metadata (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionMasterRegister → Nat) :
    let after := (extractionResourceSetupTemplate tm backward).counters cs
    after (.inr 0)=cs (.inl 2) ∧ after (.inr 1)=(if backward then 0 else cs (.inl 9)-1) ∧
      after (.inr 11)=cs (.inl 11)-cs (.inl 8)+tickSizeBound tm ∧
      after (.inr 18)=(if backward then cs (.inl 11) else cs (.inl 10)) ∧
      after (.inr 26)=cs (.inl 9) ∧ after (.inr 27)=cs (.inl 4)-1 ∧ after (.inr 16)=0 := by
  have hc : ∀ t : ExtractionMasterRegister → Nat,
      (counterPairRetreatTemplate (.inr 11) (.inr 25) (.inr 8)).counters t=
        Function.update (Function.update (Function.update t (.inr 11) (t (.inr 11)-t (.inr 8)))
          (.inr 25) (t (.inr 25)-t (.inr 8))) (.inr 8) 0 :=
    fun t => counterPairRetreatTemplate_counters _ _ _ (by decide) (by decide) (by decide) t
  cases backward <;> simp [extractionResourceSetupTemplate,extractionResourceSetupPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,counterAffineCopyProgramTemplate,
    decrementProgramTemplate,counterAffineAccumulationProgramTemplate,AffineAtom.apply,cleanupCounters_apply,hc,extractionForestScratch]

end ShiReversibleGenerator
