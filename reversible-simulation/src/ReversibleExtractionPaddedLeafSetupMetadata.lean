import ReversibleExtractionPaddedLeafSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionPaddedLeafSetupTemplate_source_frame (tm : Turing.FinTM2)
    (cs : ExtractionPaddedRegister → Nat) (q : ExtractionPaddedRegister)
    (hq : q ∈ ([0,1,4,11,16,18] : List ExtractionPaddedRegister)) :
    (extractionPaddedLeafSetupTemplate tm).counters cs q=cs q := by
  have ht := extractionWholeSizeProgramTemplate_source_frame tm cs q (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  change extractionPaddedRootSetupTemplate.counters ((extractionWholeSizeProgramTemplate tm).counters cs) q=cs q
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simpa [extractionPaddedRootSetupTemplate_counters,Function.update_apply,
    cleanupCounters_apply] using ht

/-- The executed runtime setup supplies exact original-formula roots and all concrete pass metadata. -/
theorem extractionPaddedLeafSetupTemplate_metadata (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionPaddedRegister → Nat) :
    let after := (extractionPaddedLeafSetupTemplate tm).counters cs
    after 0=cs 0 ∧ after 1=cs 1 ∧ after 4=cs 4 ∧ after 11=cs 11 ∧ after 18=cs 18 ∧
      after 24=(extractionFormula tm e (after 0) (after 1)).result (after 18) ∧
      after 25=after 18+after 4 ∧ after 2=0 ∧ after 9=after 0+1 ∧ after 22=after 0+1 ∧
      after 7=0 ∧ after 17=0 ∧
      after 20=after 18+((extractionNaturalTermRange tm e (after 0) (after 1) 0 (after 0+1)).map (fun p => p.size+4)).sum := by
  let t := (extractionWholeSizeProgramTemplate tm).counters cs
  have ht0 : t 0=cs 0 := extractionWholeSizeProgramTemplate_source_frame tm cs 0 (by simp)
  have ht1 : t 1=cs 1 := extractionWholeSizeProgramTemplate_source_frame tm cs 1 (by simp)
  have ht4 : t 4=cs 4 := extractionWholeSizeProgramTemplate_source_frame tm cs 4 (by simp)
  have ht11 : t 11=cs 11 := extractionWholeSizeProgramTemplate_source_frame tm cs 11 (by simp)
  have ht18 : t 18=cs 18 := extractionWholeSizeProgramTemplate_source_frame tm cs 18 (by simp)
  have hs : t 12=(extractionFormula tm e (t 0) (t 1)).size := by
    rw [ht0,ht1]
    exact extractionWholeSizeProgramTemplate_value tm e cs
  rcases extractionPaddedRootSetupTemplate_metadata tm e t hs with
    ⟨h0,h1,h4,h11,h18,hroot,hslot,h2,h9,h22,h7,h17,h20⟩
  exact ⟨h0.trans ht0,h1.trans ht1,h4.trans ht4,h11.trans ht11,h18.trans ht18,
    hroot,hslot,h2,h9,h22,h7,h17,h20⟩

end ShiReversibleGenerator
