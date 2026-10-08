import ReversibleTickForestLayerCount
import ReversibleInitializationForestLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem tickSymbolRowLayers_coordinates (tm : Turing.FinTM2) (capacity : Nat) (stack : tm.K) (i : Fin capacity) :
    tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) capacity i.val =
      (List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
        formulaElementaryLayers ((tickFormulas (FormulaCfg.inputs tm capacity)).cells stack i
          ((Fintype.equivFin (Option (MachineSymbol tm))).symm a))+1)).sum := by
  unfold tickCoordinateListSymbolicLayers tickSymbolRowKinds
  simp only [List.map_map,Function.comp_def]
  simp_rw [tickCoordinateSymbolicLayers_bounded tm capacity i]
  simp [tickSymbolOrder,List.map_ofFn,Function.comp_def,boundedTickFormulaForKind]

theorem tickHeaderLayers_coordinates (tm : Turing.FinTM2) (capacity : Nat) (hc : 0 < capacity) :
    tickCoordinateListSymbolicLayers tm (tickHeaderKinds tm) capacity 0 =
      (List.ofFn (fun l : Fin (Fintype.card (Option tm.Λ)) =>
        formulaElementaryLayers ((tickFormulas (FormulaCfg.inputs tm capacity)).label
          ((Fintype.equivFin (Option tm.Λ)).symm l))+1)).sum+
      (List.ofFn (fun v : Fin (Fintype.card tm.σ) =>
        formulaElementaryLayers ((tickFormulas (FormulaCfg.inputs tm capacity)).memory
          ((Fintype.equivFin tm.σ).symm v))+1)).sum := by
  let i : Fin capacity := ⟨0,hc⟩
  have h : ∀ kind, tickCoordinateSymbolicLayers tm kind capacity 0 =
      formulaElementaryLayers (boundedTickFormulaForKind tm capacity i kind)+1 := by
    intro kind
    exact tickCoordinateSymbolicLayers_bounded tm capacity i kind
  unfold tickCoordinateListSymbolicLayers
  simp_rw [h]
  simp only [tickHeaderKinds,List.map_append,List.sum_append,List.map_ofFn,Function.comp_def,boundedTickFormulaForKind]

/-- Runtime layer counting is exactly the established tick forest's elementary-layer sum. -/
theorem tickForestLayerCount_coordinates (tm : Turing.FinTM2) (capacity : Nat) (hc : 0 < capacity) :
    tickForestLayerCount tm capacity = ((tickForest tm capacity).map (fun p => formulaElementaryLayers p+1)).sum := by
  have h := configurationBitEquiv_ofFn tm capacity (fun coordinate =>
    formulaElementaryLayers ((tickFormulas (FormulaCfg.inputs tm capacity)).bitFormula
      (configurationBitEquiv tm capacity coordinate))+1)
  have hs := congrArg List.sum h
  simp only [FormulaCfg.bitFormula,Equiv.symm_apply_apply,List.sum_append,sum_flatten_blocks,
    List.map_flatten,List.map_ofFn,List.map_map,Function.comp_def] at hs
  unfold tickForestLayerCount
  rw [tickHeaderLayers_coordinates tm capacity hc]
  simp_rw [tickSymbolRowDescendingLayers_ofFn,tickSymbolRowLayers_coordinates]
  simpa only [tickForest,tickStackOrder,FormulaCfg.bitFormula,List.map_ofFn,Function.comp_def,Equiv.apply_symm_apply,Nat.add_assoc] using hs.symm

end ShiReversibleGenerator
