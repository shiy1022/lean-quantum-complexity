import ReversibleExtractionInversePrefixFullCertificate
import ReversibleExtractionInverseClosingFullCertificate
import ReversibleExtractionInverseClosingHandoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Runtime prefix, finite coordinate handoff, then closing prepends the full inverse extraction payload. -/
noncomputable def extractionInversePassTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  sequenceProgramTemplate (extractionInversePrefixLoopTemplate tm e stride)
    (sequenceProgramTemplate extractionInverseClosingHandoffTemplate (extractionInverseClosingLoopTemplate tm))

theorem extractionInversePassTemplate_embeds (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) : (extractionInversePassTemplate tm e stride).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionInversePrefixLoopTemplate_embeds tm e stride)
    (sequenceProgramTemplate_embeds _ _ extractionInverseClosingHandoffTemplate_embeds
      (extractionInverseClosingLoopTemplate_embeds tm))

theorem extractionInversePassTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) : (extractionInversePassTemplate tm e stride).Runs :=
  sequenceProgramTemplate_run _ _ (extractionInversePrefixLoopTemplate_embeds tm e stride)
    (extractionInversePrefixLoopTemplate_run tm e stride)
    (sequenceProgramTemplate_run _ _ extractionInverseClosingHandoffTemplate_embeds
      extractionInverseClosingHandoffTemplate_run (extractionInverseClosingLoopTemplate_run tm))

theorem extractionInversePassTemplate_ready (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hb : cs 17=0) :
    (extractionInversePassTemplate tm e stride).ready cs := by
  let t := (extractionInversePrefixLoopTemplate tm e stride).counters cs
  have ht : t 17=0 := (descendingProgramTemplate_point_frame
    (extractionInversePrefixTraversalStepTemplate tm e stride) 22 17 (by decide)
    (extractionInversePrefixTraversalStepTemplate_buffer tm e stride) cs).trans hb
  refine ⟨extractionInversePrefixLoopTemplate_ready tm e stride cs hb,
    extractionInverseClosingHandoffTemplate_ready t,?_⟩
  apply extractionInverseClosingLoopTemplate_ready tm
  simpa [extractionInverseClosingHandoffTemplate_counters,cleanupCounters_apply] using ht

theorem extractionInversePassTemplate_resources (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    (extractionInversePassTemplate tm e stride).CounterBound bound ∧
      (extractionInversePassTemplate tm e stride).PolynomiallyTimed bound := by
  obtain ⟨first,hfirst,hfirstExit⟩ := extractionInversePrefixLoopTemplate_resources tm e stride bound
  obtain ⟨⟨second,hsecondExit⟩,hsecond⟩ := extractionInverseClosingHandoffTemplate_resources first
  obtain ⟨third,hthird,hthirdExit⟩ := extractionInverseClosingLoopTemplate_resources tm second
  refine ⟨⟨third,?_⟩,?_⟩
  · intro n cs hb q
    exact hthirdExit n _ (hsecondExit n _ (hfirstExit n cs hb)) q
  · apply sequenceProgramTemplate_polynomial _ _ bound first
    · exact hfirst
    · intro n cs hb hr
      exact hfirstExit n cs hb
    · exact sequenceProgramTemplate_polynomial _ _ first second hsecond
        (fun n cs hb _ => hsecondExit n cs hb) hthird

end ShiReversibleGenerator
