import ReversibleNaturalTickInputs
import ReversibleConfigurationCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleTM
open ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Cell addresses use only fixed ranks and affine runtime capacity/index arithmetic. -/
noncomputable def naturalConfigurationAddress (tm : Turing.FinTM2) (capacity : Nat) :
    NaturalConfigurationBit tm → Nat
  | .inl (.inl l) => ((Fintype.equivFin (Option tm.Λ)) l).val
  | .inl (.inr v) => Fintype.card (Option tm.Λ) + ((Fintype.equivFin tm.σ) v).val
  | .inr ((k, i), a) => Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
      (((Fintype.equivFin tm.K) k).val * capacity + i) * Fintype.card (Option (MachineSymbol tm)) +
      ((Fintype.equivFin (Option (MachineSymbol tm))) a).val

theorem naturalConfigurationAddress_coordinate (tm : Turing.FinTM2) (capacity : Nat)
    (b : ConfigurationBit tm capacity) :
    naturalConfigurationAddress tm capacity (naturalConfigurationCoordinate b) =
      (configurationBitEquiv tm capacity b).val := by
  cases b with
  | inl z => cases z with
    | inl l => exact (configurationBitEquiv_label_val tm capacity l).symm
    | inr v => exact (configurationBitEquiv_memory_val tm capacity v).symm
  | inr z => exact (configurationBitEquiv_cell_val tm capacity z.1.1 z.1.2 z.2).symm

theorem naturalInputAddress_value (tm : Turing.FinTM2) (capacity : Nat)
    (i : Fin (configurationWidth tm capacity)) :
    naturalConfigurationAddress tm capacity (naturalInputAddress tm capacity i) = i.val := by
  simpa only [naturalInputAddress, Equiv.apply_symm_apply] using
    naturalConfigurationAddress_coordinate tm capacity ((configurationBitEquiv tm capacity).symm i)

theorem FormulaCfg.rename_bitFormula {tm : Turing.FinTM2} {capacity : Nat} {ι κ : Type}
    (p : FormulaCfg tm capacity ι) (r : ι → κ) (i : Fin (configurationWidth tm capacity)) :
    (p.rename r).bitFormula i = (p.bitFormula i).rename r := by
  unfold FormulaCfg.bitFormula
  cases (configurationBitEquiv tm capacity).symm i with
  | inl z => cases z <;> rfl
  | inr z => rfl

/-- The natural-address formula compiler emits precisely the established tick assignments. -/
theorem naturalTickFormulas_rawCompile (tm : Turing.FinTM2) (capacity base : Nat)
    (i : Fin (configurationWidth tm capacity)) :
    (((naturalTickFormulas capacity (naturalInputFormulas tm)).restrict capacity).bitFormula i).rawCompile
      (naturalConfigurationAddress tm capacity) base =
      ((tickFormulas (FormulaCfg.inputs tm capacity)).bitFormula i).rawCompile Fin.val base := by
  rw [naturalTickFormulas_inputs, FormulaCfg.rename_bitFormula, Formula.rename_rawCompile]
  have h : (fun j => naturalConfigurationAddress tm capacity (naturalInputAddress tm capacity j)) =
      (Fin.val : Fin (configurationWidth tm capacity) → Nat) := by
    funext j; exact naturalInputAddress_value tm capacity j
  rw [h]

end ShiReversibleTM
