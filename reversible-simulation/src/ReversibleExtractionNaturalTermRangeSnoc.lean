import ReversibleExtractionNaturalTermRange

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The ascending original list splits at its final length, matching a descending printer step. -/
theorem extractionNaturalTermRange_snoc (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j ell k : Nat) :
    extractionNaturalTermRange tm e capacity j ell (k+1)=
      extractionNaturalTermRange tm e capacity j ell k ++ [extractionNaturalTerm tm e capacity (ell+k) j] := by
  induction k generalizing ell with
  | zero => simp [extractionNaturalTermRange]
  | succ k ih =>
    change extractionNaturalTerm tm e capacity ell j :: extractionNaturalTermRange tm e capacity j (ell+1) (k+1) =
      (extractionNaturalTerm tm e capacity ell j :: extractionNaturalTermRange tm e capacity j (ell+1) k) ++
        [extractionNaturalTerm tm e capacity (ell+(k+1)) j]
    rw [ih]
    simp only [List.cons_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end ShiReversibleGenerator
