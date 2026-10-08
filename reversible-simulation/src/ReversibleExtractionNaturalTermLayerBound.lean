import ReversibleExtractionNaturalTermRange
import ReversibleExtractionTermSizeBudget
import ReversibleFormulaLayerCount

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionNaturalTerm_layers_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) (hell : ell ≤ capacity) :
    formulaElementaryLayers (extractionNaturalTerm tm e capacity ell j)+2 ≤
      37*(10+Fintype.card (Option (MachineSymbol tm))*7)+2 := by
  have he := extractionNaturalTerm_size tm e capacity ell j hell
  have hb := extractionSizeContribution_bound tm ell j
  have hs : (extractionNaturalTerm tm e capacity ell j).size ≤
      10+Fintype.card (Option (MachineSymbol tm))*7 := by omega
  exact Nat.add_le_add_right ((formulaElementaryLayers_bound _).trans (Nat.mul_le_mul_left 37 hs)) 2

/-- Original prefix layer counts grow linearly in the actual number of remaining terms. -/
theorem extractionNaturalTermRange_layers_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j ell k : Nat) (hlimit : ell+k ≤ capacity+1) :
    ((extractionNaturalTermRange tm e capacity j ell k).map (fun p => formulaElementaryLayers p+2)).sum ≤
      k*(37*(10+Fintype.card (Option (MachineSymbol tm))*7)+2) := by
  induction k generalizing ell with
  | zero => simp [extractionNaturalTermRange]
  | succ k ih =>
    have ht := extractionNaturalTerm_layers_bound tm e capacity ell j (by omega)
    have hi := ih (ell+1) (by omega)
    simpa only [extractionNaturalTermRange,List.map_cons,List.sum_cons,Nat.succ_mul,Nat.add_comm] using
      Nat.add_le_add ht hi

end ShiReversibleGenerator
