import ReversibleConfigurationHeaderGenerator
import ReversibleConfigurationCoordinates

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding ShiReversibleFormula
open scoped Classical
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

def initializationFormulaPayload {n : Nat} (p : Formula (Fin n)) (backward : Bool) (base : Nat) :=
  let nodes := p.paddedCompile (fun i => i.val) base 17
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

/-- Label literals print the same nodes at the same addresses as the established initializer. -/
theorem configurationHeader_label_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) (j : Fin (Fintype.card (Option tm.Λ))) :
    constantInitializationPayload
      (oneHot (some tm.main) ((Fintype.equivFin (Option tm.Λ)).symm j)) backward (n + 18 * j.val) =
      initializationFormulaPayload
        ((initialFormulas tm e capacity n).label ((Fintype.equivFin (Option tm.Λ)).symm j)) backward
        (n + 18 * (configurationBitEquiv tm capacity
          (.inl (.inl ((Fintype.equivFin (Option tm.Λ)).symm j)))).val) := by
  classical
  simp [configurationBitEquiv_label_val, initializationFormulaPayload,
    constantInitializationPayload, initialFormulas, Formula.paddedCompile,
    Formula.rawCompile, Formula.size, Formula.result]

/-- Memory literals agree with the existing finite enumeration and padded compiler. -/
theorem configurationHeader_memory_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) (j : Fin (Fintype.card tm.σ)) :
    constantInitializationPayload
      (oneHot tm.initialState ((Fintype.equivFin tm.σ).symm j)) backward
      (n + 18 * (Fintype.card (Option tm.Λ) + j.val)) =
      initializationFormulaPayload
        ((initialFormulas tm e capacity n).memory ((Fintype.equivFin tm.σ).symm j)) backward
        (n + 18 * (configurationBitEquiv tm capacity
          (.inl (.inr ((Fintype.equivFin tm.σ).symm j)))).val) := by
  classical
  simp [configurationBitEquiv_memory_val, initializationFormulaPayload,
    constantInitializationPayload, initialFormulas, Formula.paddedCompile,
    Formula.rawCompile, Formula.size, Formula.result]

end ShiReversibleGenerator
