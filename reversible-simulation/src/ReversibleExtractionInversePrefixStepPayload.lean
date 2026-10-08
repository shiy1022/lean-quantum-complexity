import ReversibleExtractionInversePrefixStepMetadata
import ReversibleExtractionForwardPrefixStepPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The inverse prefix body emits exactly the reversed original term-plus-negation compiler block. -/
theorem extractionInversePrefixStepTemplate_payload (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat)
    (hell : cs 2 ≤ cs 0) :
    let p := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
      (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
    let inputs := fun i => cs 11+stride*naturalConfigurationAddress tm (cs 0)
      (naturalInputAddress tm (cs 0) i)
    (extractionInversePrefixStepTemplate tm e stride).bytes cs=
      (((p.rawCompile inputs (cs 18) ++ [RawAssignment.neg (p.result (cs 18)) (cs 18+p.size)]).reverse).map
        (rawAssignmentPayload true)).flatten := by
  dsimp only
  let p := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
    (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht : ∀ q ∈ ([0,1,2,11,18] : List ExtractionTermRegister),t q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have h0 := ht 0 (by simp)
  have h1 := ht 1 (by simp)
  have h2 := ht 2 (by simp)
  have h11 := ht 11 (by simp)
  have h18 := ht 18 (by simp)
  have hu18 : u 18=t 18 := extractionBoundTermPrinterTemplate_frame tm e stride true t 18
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hu12 : u 12=t 12 := extractionBoundTermPrinterTemplate_frame tm e stride true t 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs : t 12=p.size+4 := extractionTermSizeProgramTemplate_exact tm e cs hell
  have hp := extractionBoundTermPrinterTemplate_payload tm e stride true t (by simpa only [h2,h0] using hell)
  dsimp only at hp
  rw [h0,h1,h2,h11,h18] at hp
  have hn := extractionTermNegationPrinterTemplate_payload true u
  rw [hu18,hu12,h18,hs] at hn
  have hpos := p.size_pos
  have hn1 : cs 18+(p.size+4)-5=cs 18+p.size-1 := by omega
  have hn2 : cs 18+p.size-1+1=cs 18+p.size := by omega
  rw [hn1,hn2] at hn
  change extractionPrefixAdvanceTemplate.bytes v ++
    (extractionTermNegationPrinterTemplate true).bytes u ++
    (extractionBoundTermPrinterTemplate tm e stride true).bytes t ++
    (extractionTermSizeProgramTemplate tm).bytes cs=_
  rw [extractionPrefixAdvanceTemplate_bytes,hp,hn,extractionTermSizeProgramTemplate_bytes]
  simp [List.reverse_append,List.map_append,List.flatten_append,Formula.result,p]

end ShiReversibleGenerator
