import ReversibleExtractionForwardPrefixStepReady
import ReversibleExtractionForwardTermRetreatMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual prefix step prints the original selected term followed by its original negation. -/
theorem extractionForwardPrefixStepTemplate_payload (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat)
    (hell : cs 2 ≤ cs 0) :
    let p := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
      (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
    let base := cs 18-(p.size+1)
    let inputs := fun i => cs 11+stride*naturalConfigurationAddress tm (cs 0)
      (naturalInputAddress tm (cs 0) i)
    (extractionForwardPrefixStepTemplate tm e stride).bytes cs=
      ((p.rawCompile inputs base ++ [RawAssignment.neg (p.result base) (base+p.size)]).map
        (rawAssignmentPayload false)).flatten := by
  dsimp only
  let p := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
    (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
  let t := (extractionForwardTermRetreatTemplate tm).counters cs
  let u := (extractionTermNegationPrinterTemplate false).counters t
  have ht : ∀ q ∈ ([0,1,2,11] : List ExtractionTermRegister),t q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact (extractionForwardTermRetreatTemplate_frame tm cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hu : ∀ q ∈ ([0,1,2,11,18] : List ExtractionTermRegister),u q=t q := by
    intro q hq
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame false t _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h0 := (hu 0 (by simp)).trans (ht 0 (by simp))
  have h1 := (hu 1 (by simp)).trans (ht 1 (by simp))
  have h2 := (hu 2 (by simp)).trans (ht 2 (by simp))
  have h11 := (hu 11 (by simp)).trans (ht 11 (by simp))
  have hc : extractionSizeContribution tm (cs 2) (cs 1)=p.size+4 :=
    extractionSizeContribution_exact tm e (cs 0) (cs 2) (cs 1) hell
  have hb : t 18=cs 18-(p.size+1) := by
    dsimp only [t]
    rw [extractionForwardTermRetreatTemplate_base, hc]
    congr 1
  have hs : t 12=p.size+4 := (extractionForwardTermRetreatTemplate_size tm cs).trans hc
  have h18 := (hu 18 (by simp)).trans hb
  have hp := extractionBoundTermPrinterTemplate_payload tm e stride false u (by simpa only [h2,h0] using hell)
  dsimp only at hp
  rw [h0,h1,h2,h11,h18] at hp
  have hn := extractionTermNegationPrinterTemplate_payload false t
  rw [hb,hs] at hn
  have hpos := p.size_pos
  have hn1 : cs 18-(p.size+1)+(p.size+4)-5=cs 18-(p.size+1)+p.size-1 := by omega
  have hn2 : cs 18-(p.size+1)+p.size-1+1=cs 18-(p.size+1)+p.size := by omega
  rw [hn1,hn2] at hn
  change (extractionBoundTermPrinterTemplate tm e stride false).bytes u ++
    (extractionTermNegationPrinterTemplate false).bytes t ++
    (extractionForwardTermRetreatTemplate tm).bytes cs=_
  rw [hp,hn,extractionForwardTermRetreatTemplate_bytes]
  simp [List.map_append,List.flatten_append,Formula.result,p]

end ShiReversibleGenerator
