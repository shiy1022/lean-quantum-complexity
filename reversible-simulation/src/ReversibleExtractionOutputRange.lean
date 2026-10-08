import ReversibleMachineExtraction
import Mathlib.Data.List.OfFn

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- An increasing range of the original output formulas, with runtime natural coordinates. -/
noncomputable def extractionOutputRange (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity start count : Nat) : List (Formula (Fin (configurationWidth tm capacity))) :=
  List.ofFn (fun i : Fin count => extractionFormula tm e capacity (start+i.val))

theorem extractionOutputRange_cons (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity start count : Nat) :
    extractionOutputRange tm e capacity start (count+1)=extractionFormula tm e capacity start ::
      extractionOutputRange tm e capacity (start+1) count := by
  simp only [extractionOutputRange,List.ofFn_succ,Fin.val_zero,Nat.add_zero,Fin.val_succ]
  congr 2
  funext i
  congr 1
  omega

theorem extractionOutputRange_snoc (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity start count : Nat) :
    extractionOutputRange tm e capacity start (count+1)=extractionOutputRange tm e capacity start count ++
      [extractionFormula tm e capacity (start+count)] := by
  simp only [extractionOutputRange]
  rw [List.ofFn_succ']
  simp only [Fin.val_castSucc,Fin.val_last,List.concat_eq_append]

theorem extractionOutputRange_original (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity : Nat) : extractionOutputRange tm e capacity 0 (2*capacity+1)=extractionForest tm e capacity := by
  simp [extractionOutputRange,extractionForest]

end ShiReversibleGenerator
