import ReversibleExtractionTermSizes

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Exact amount added to the right-fold suffix size for one selected length. -/
noncomputable def extractionSizeContribution (tm : Turing.FinTM2) (ell j : Nat) : Nat :=
  (if ell=0 then 9 else 10)+
    (if ell+1 ≤ j ∧ j ≤ 2*ell then Fintype.card (Option (MachineSymbol tm))*7 else 0)

/-- In the enumerated length range, the third payload-capacity test follows from the first two. -/
theorem extractionSizeContribution_exact (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) (hell : ell ≤ capacity) :
    extractionSizeContribution tm ell j=
      (Formula.conj (lengthFlag (extractionEmpty tm capacity) ell)
        (outputValue (extractionPayload tm e capacity) ell j)).size+4 := by
  rw [extraction_selectedTerm_size]
  have h : (ell+1 ≤ j ∧ j < 2*ell+1 ∧ j-ell-1 < capacity) ↔ (ell+1 ≤ j ∧ j ≤ 2*ell) := by omega
  simp only [extractionSizeContribution,h]
  split <;> omega

/-- Selected output formula size is a finite sum of the same arithmetic contributions. -/
theorem extractionFormula_size_exact (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j : Nat) :
    (extractionFormula tm e capacity j).size=
      1+((List.finRange (capacity+1)).map (fun ell => extractionSizeContribution tm ell.val j)).sum := by
  unfold extractionFormula outputFormula selectedFin
  rw [disjoin_size_exact]
  congr 1
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro ell hel
  exact (extractionSizeContribution_exact tm e capacity ell.val j (Nat.le_of_lt_succ ell.isLt)).symm

end ShiReversibleGenerator
