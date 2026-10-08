import ReversibleExtractionNaturalTermRangeSnoc
import ReversibleFormulaRenaming

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Runtime length enumeration is exactly the original increasing finite range. -/
theorem extractionNaturalTermRange_ofFn (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j ell k : Nat) :
    extractionNaturalTermRange tm e capacity j ell k=
      List.ofFn (fun i : Fin k => extractionNaturalTerm tm e capacity (ell+i.val) j) := by
  induction k with
  | zero => simp [extractionNaturalTermRange]
  | succ k ih =>
    rw [extractionNaturalTermRange_snoc,ih,List.ofFn_succ']
    simp only [Fin.val_castSucc,Fin.val_last,List.concat_eq_append]

/-- The exact original output formula is retained; only its input coordinate representation is renamed. -/
theorem extractionNaturalFormula_original (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j : Nat) :
    disjoin (extractionNaturalTermRange tm e capacity j 0 (capacity+1))=
      (extractionFormula tm e capacity j).rename (naturalInputAddress tm capacity) := by
  unfold extractionFormula outputFormula selectedFin
  rw [rename_disjoin,extractionNaturalTermRange_ofFn]
  simp only [List.ofFn_eq_map,List.map_map,Function.comp_def,Nat.zero_add,extractionNaturalTerm]

theorem extractionNaturalFormula_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j : Nat) :
    1+((extractionNaturalTermRange tm e capacity j 0 (capacity+1)).map (fun p => p.size+4)).sum=
      (extractionFormula tm e capacity j).size := by
  rw [←disjoin_size_exact,extractionNaturalFormula_original,Formula.rename_size]

/-- The false base plus three closing wires per term is the exact original compiler endpoint. -/
theorem extractionClosingEndpoint_sum {ι : Type} (ps : List (Formula ι)) :
    (ps.map (fun p => p.size+1)).sum+3*ps.length=(ps.map (fun p => p.size+4)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
    omega

end ShiReversibleGenerator
