import ReversibleExtractionWholeSizeResources
import ReversibleExtractionWholeSizeSourceFrames
import ReversibleExtractionPaddedRootSetupResources
import ReversibleExtractionPaddedRootSetupMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Compute the exact formula size, then initialize both emission passes and the two distinct roots. -/
noncomputable def extractionPaddedLeafSetupTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (extractionWholeSizeProgramTemplate tm) extractionPaddedRootSetupTemplate

theorem extractionPaddedLeafSetupTemplate_embeds (tm : Turing.FinTM2) :
    (extractionPaddedLeafSetupTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionWholeSizeProgramTemplate_embeds tm) extractionPaddedRootSetupTemplate_embeds

theorem extractionPaddedLeafSetupTemplate_run (tm : Turing.FinTM2) :
    (extractionPaddedLeafSetupTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (extractionWholeSizeProgramTemplate_embeds tm)
    (extractionWholeSizeProgramTemplate_run tm) extractionPaddedRootSetupTemplate_run

theorem extractionPaddedLeafSetupTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionPaddedRegister → Nat) :
    (extractionPaddedLeafSetupTemplate tm).ready cs :=
  ⟨extractionWholeSizeProgramTemplate_ready tm cs,extractionPaddedRootSetupTemplate_ready _⟩

theorem extractionPaddedLeafSetupTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionPaddedRegister → Nat) :
    (extractionPaddedLeafSetupTemplate tm).bytes cs=[] := by
  change extractionPaddedRootSetupTemplate.bytes ((extractionWholeSizeProgramTemplate tm).counters cs) ++
    (extractionWholeSizeProgramTemplate tm).bytes cs=[]
  rw [extractionPaddedRootSetupTemplate_bytes,extractionWholeSizeProgramTemplate_bytes]
  rfl

theorem extractionPaddedLeafSetupTemplate_resources (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionPaddedLeafSetupTemplate tm).CounterBound bound ∧
      (extractionPaddedLeafSetupTemplate tm).PolynomiallyTimed bound := by
  obtain ⟨⟨middle,hm⟩,ht⟩ := extractionWholeSizeProgramTemplate_resources tm bound
  obtain ⟨⟨final,hf⟩,hr⟩ := extractionPaddedRootSetupTemplate_resources middle
  exact ⟨⟨final,fun n cs hb q => hf n _ (hm n cs hb) q⟩,
    sequenceProgramTemplate_polynomial _ _ bound middle ht (fun n cs hb _ => hm n cs hb) hr⟩

/-- Ready scratch comes from the executed setup, not from an assumed formula-emitter endpoint. -/
theorem extractionPaddedLeafSetupTemplate_scratch (tm : Turing.FinTM2) (cs : ExtractionPaddedRegister → Nat) :
    (extractionPaddedLeafSetupTemplate tm).counters cs 7=0 ∧
      (extractionPaddedLeafSetupTemplate tm).counters cs 17=0 := by
  change extractionPaddedRootSetupTemplate.counters ((extractionWholeSizeProgramTemplate tm).counters cs) 7=0 ∧
    extractionPaddedRootSetupTemplate.counters ((extractionWholeSizeProgramTemplate tm).counters cs) 17=0
  simp [extractionPaddedRootSetupTemplate_counters,cleanupCounters_apply]

end ShiReversibleGenerator
