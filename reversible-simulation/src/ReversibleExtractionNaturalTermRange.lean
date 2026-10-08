import ReversibleExtractionTermSchema
import ReversibleExtractionDisjoinPasses

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Original selected extraction terms, with all input coordinates in one capacity-independent type. -/
noncomputable def extractionNaturalTerm (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) : Formula (NaturalConfigurationBit tm) :=
  (Formula.conj (lengthFlag (extractionEmpty tm capacity) ell)
    (outputValue (extractionPayload tm e capacity) ell j)).rename (naturalInputAddress tm capacity)

noncomputable def extractionNaturalTermRange (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j : Nat) : Nat → Nat → List (Formula (NaturalConfigurationBit tm))
  | _,0 => []
  | ell,k+1 => extractionNaturalTerm tm e capacity ell j::extractionNaturalTermRange tm e capacity j (ell+1) k

theorem extractionNaturalTerm_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) (hell : ell ≤ capacity) :
    (extractionNaturalTerm tm e capacity ell j).size+4=extractionSizeContribution tm ell j := by
  rw [extractionNaturalTerm,Formula.rename_size]
  exact (extractionSizeContribution_exact tm e capacity ell j hell).symm

theorem extractionNaturalTermRange_length (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j ell k : Nat) : (extractionNaturalTermRange tm e capacity j ell k).length=k := by
  induction k generalizing ell with
  | zero => rfl
  | succ k ih => simp [extractionNaturalTermRange,ih]

/-- Remaining original terms determine an endpoint with at least three closing wires whenever a term remains. -/
theorem extractionNaturalTermRange_endpoint (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j ell k base : Nat) :
    3 ≤ base+((extractionNaturalTermRange tm e capacity j ell (k+1)).map (fun p => p.size+4)).sum := by
  simp only [extractionNaturalTermRange,List.map_cons,List.sum_cons]
  omega

end ShiReversibleGenerator
