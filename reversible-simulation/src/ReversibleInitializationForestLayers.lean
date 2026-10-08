import ReversibleRankedStackExactLayers
import ReversibleConfigurationEnumeration

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem sum_flatten_blocks (blocks : List (List Nat)) :
    blocks.flatten.sum = (blocks.map List.sum).sum := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.flatten_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

noncomputable def initializationHeaderLayerCount (tm : Turing.FinTM2) : Nat :=
  ((initializationHeaderRanks tm).map (fun ar =>
    formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum

noncomputable def initializationForestLayerCount (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) : Nat :=
  ((initialForest tm e capacity n).map (fun p => formulaElementaryLayers p + 1)).sum

theorem initializationHeaderLayerCount_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) :
    initializationHeaderLayerCount tm =
      (List.ofFn (fun j : Fin (Fintype.card (Option tm.Λ)) =>
        formulaElementaryLayers ((initialFormulas tm e capacity n).label
          ((Fintype.equivFin (Option tm.Λ)).symm j)) + 1)).sum +
      (List.ofFn (fun j : Fin (Fintype.card tm.σ) =>
        formulaElementaryLayers ((initialFormulas tm e capacity n).memory
          ((Fintype.equivFin tm.σ).symm j)) + 1)).sum := by
  classical
  simp only [initializationHeaderLayerCount, initializationHeaderRanks,
    List.map_append, List.sum_append, List.map_ofFn, Function.comp_def]
  rfl

/-- The count is the sum over the pre-existing forest, with precisely its configuration-coordinate order. -/
theorem initializationForestLayerCount_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) :
    initializationForestLayerCount tm e capacity n = initializationHeaderLayerCount tm +
      (List.ofFn (fun k : Fin (Fintype.card tm.K) =>
        initializationStackLayerCount tm e capacity n ((Fintype.equivFin tm.K).symm k))).sum := by
  classical
  have h := configurationBitEquiv_ofFn tm capacity (fun coordinate =>
    formulaElementaryLayers ((initialFormulas tm e capacity n).bitFormula
      (configurationBitEquiv tm capacity coordinate)) + 1)
  have hs := congrArg List.sum h
  simp only [FormulaCfg.bitFormula, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    List.sum_append, sum_flatten_blocks, List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def] at hs
  rw [initializationHeaderLayerCount_coordinates tm e capacity n]
  simpa only [initializationForestLayerCount, initialForest, List.map_ofFn,
    initializationStackLayerCount, FormulaCfg.bitFormula, Function.comp_def, Nat.add_assoc] using hs

end ShiReversibleGenerator
