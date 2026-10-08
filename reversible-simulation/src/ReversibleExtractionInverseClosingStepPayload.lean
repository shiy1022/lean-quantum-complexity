import ReversibleExtractionInverseClosingStep

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Exact inverse closing nodes use the retreated original term base and current suffix endpoint. -/
theorem extractionInverseClosingStepTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) (hend : 3 ≤ cs 20) :
    let term := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
      (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
    let base := cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3)
    let nodes := [RawAssignment.neg (cs 20-3) (cs 20-2),
      .conj (base+term.size) (cs 20-2) (cs 20-1),.neg (cs 20-1) (cs 20)]
    (extractionInverseClosingStepTemplate tm).bytes cs=
      (nodes.reverse.map (rawAssignmentPayload true)).flatten := by
  dsimp only
  let t := (extractionInverseClosingRetreatTemplate tm).counters cs
  have hf : ∀ q ∈ ([0,1,2,20] : List ExtractionTermRegister),t q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact (extractionInverseClosingRetreatTemplate_frame tm cs _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h0 := hf 0 (by simp)
  have h1 := hf 1 (by simp)
  have h2 := hf 2 (by simp)
  have h20 := hf 20 (by simp)
  have h18 : t 18=cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) :=
    extractionInverseClosingRetreatTemplate_base tm cs
  have h := extractionBoundClosingPrinterTemplate_payload tm e true t
    (by simpa only [h2,h0] using hell) (by simpa only [h20] using hend)
  rw [extractionInverseClosingStepTemplate_bytes]
  exact h.trans (by
    rw [h0,h1,h2,h20,h18,if_pos rfl])

end ShiReversibleGenerator
