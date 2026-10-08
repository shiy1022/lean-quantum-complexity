import ReversibleConfigurationHeaderPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def initializationHeaderBlocks (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) : List (List Bool) :=
  List.ofFn (fun j : Fin (Fintype.card (Option tm.Λ)) =>
    initializationFormulaPayload ((initialFormulas tm e capacity n).label
      ((Fintype.equivFin (Option tm.Λ)).symm j)) backward
      (n + 18 * (configurationBitEquiv tm capacity
        (.inl (.inl ((Fintype.equivFin (Option tm.Λ)).symm j)))).val)) ++
  List.ofFn (fun j : Fin (Fintype.card tm.σ) =>
    initializationFormulaPayload ((initialFormulas tm e capacity n).memory
      ((Fintype.equivFin tm.σ).symm j)) backward
      (n + 18 * (configurationBitEquiv tm capacity
        (.inl (.inr ((Fintype.equivFin tm.σ).symm j)))).val))

/-- The entire actual header printer agrees with the established label and memory formula blocks. -/
theorem configurationHeader_forest_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) :
    configurationHeaderPayload tm backward n =
      (if backward then (initializationHeaderBlocks tm e capacity n backward).reverse
       else initializationHeaderBlocks tm e capacity n backward).flatten := by
  classical
  have hblocks : ((initializationHeaderRanks tm).map
      (fun ar => constantInitializationPayload ar.1 backward (n + 18 * ar.2))) =
      initializationHeaderBlocks tm e capacity n backward := by
    simp only [initializationHeaderRanks, List.map_append, List.map_ofFn,
      Function.comp_def, initializationHeaderBlocks]
    congr 1
    · apply congrArg List.ofFn
      funext j
      exact configurationHeader_label_payload tm e capacity n backward j
    · apply congrArg List.ofFn
      funext j
      exact configurationHeader_memory_payload tm e capacity n backward j
  cases backward <;>
    simp only [configurationHeaderPayload, Bool.false_eq_true, if_false, if_true,
      List.flatMap_def, List.map_reverse, hblocks]

end ShiReversibleGenerator
