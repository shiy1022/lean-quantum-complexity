import ReversibleFormulaLayerCount
import ReversibleExtractionNaturalFormulaAgreement
import ReversibleExtractionInversePass
import ReversibleExtractionInversePrefixLoopCount
import ReversibleExtractionInversePrefixSourceFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula
variable {ι : Type}

theorem formulaElementaryLayers_disjoin_exact (ps : List (Formula ι)) :
    formulaElementaryLayers (disjoin ps)=(ps.map (fun p => formulaElementaryLayers p+43)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [disjoin,List.foldr_cons,Formula.disj,formulaElementaryLayers,List.map_cons,List.sum_cons]
    change formulaElementaryLayers p+2+(formulaElementaryLayers (disjoin ps)+2)+37+2=_
    rw [ih]
    omega

theorem extractionPassLayerCount_split (ps : List (Formula ι)) :
    (ps.map (fun p => formulaElementaryLayers p+2)).sum+41*ps.length=
      formulaElementaryLayers (disjoin ps) := by
  rw [formulaElementaryLayers_disjoin_exact]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
    omega

/-- The actual assembled inverse pass counts exactly the elementary layers of the original formula. -/
theorem extractionInversePassTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hell : cs 2=0) (hcount : cs 22=cs 0+1) :
    (extractionInversePassTemplate tm e stride).counters cs 16=cs 16+
      formulaElementaryLayers (disjoin (extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1))) := by
  let t := (extractionInversePrefixLoopTemplate tm e stride).counters cs
  let u := extractionInverseClosingHandoffTemplate.counters t
  let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)
  have ht0 : t 0=cs 0 := extractionInversePrefixLoopTemplate_source_frame tm e stride cs 0 (by simp)
  have ht16 : t 16=cs 16+(terms.map (fun p => formulaElementaryLayers p+2)).sum := by
    have h := extractionInversePrefixLoop_count tm e stride (cs 22) cs (by rw [hell,hcount]; omega)
    change t 16=_ at h
    simpa only [hell,hcount] using h
  have hu16 : u 16=t 16 := by simp [u,extractionInverseClosingHandoffTemplate_counters,cleanupCounters_apply]
  have hu22 : u 22=cs 0+1 := by simp [u,extractionInverseClosingHandoffTemplate_counters,ht0]
  have hl : terms.length=cs 0+1 := extractionNaturalTermRange_length tm e (cs 0) (cs 1) 0 _
  have hx := extractionPassLayerCount_split terms
  change (extractionInverseClosingLoopTemplate tm).counters u 16=cs 16+formulaElementaryLayers (disjoin terms)
  rw [extractionInverseClosingLoopTemplate_count,hu16,hu22,ht16]
  rw [hl] at hx
  omega

end ShiReversibleGenerator
