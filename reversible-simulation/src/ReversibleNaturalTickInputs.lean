import ReversibleNaturalAddressTick
import ReversibleTickRenaming

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleTM
open ShiReversibleFormula

/-- Fixed coordinate type: the runtime cell index is a natural number, not a finite type. -/
abbrev NaturalConfigurationBit (tm : Turing.FinTM2) :=
  (Option tm.Λ ⊕ tm.σ) ⊕ ((tm.K × Nat) × Option (MachineSymbol tm))

def naturalConfigurationCoordinate {tm : Turing.FinTM2} {capacity : Nat} :
    ConfigurationBit tm capacity → NaturalConfigurationBit tm
  | .inl x => .inl x
  | .inr ((k, i), a) => .inr ((k, i.val), a)

def naturalInputFormulas (tm : Turing.FinTM2) : NaturalFormulaCfg tm (NaturalConfigurationBit tm) where
  label l := .input (.inl (.inl l))
  memory v := .input (.inl (.inr v))
  cells k i a := .input (.inr ((k, i), a))

noncomputable def naturalInputAddress (tm : Turing.FinTM2) (capacity : Nat) :
    Fin (configurationWidth tm capacity) → NaturalConfigurationBit tm :=
  fun i => naturalConfigurationCoordinate ((configurationBitEquiv tm capacity).symm i)

theorem naturalInputFormulas_restrict (tm : Turing.FinTM2) (capacity : Nat) :
    (naturalInputFormulas tm).restrict capacity =
      (FormulaCfg.inputs tm capacity).rename (naturalInputAddress tm capacity) := by
  apply FormulaCfg.fields_ext
  · funext l
    simp [naturalInputFormulas, NaturalFormulaCfg.restrict, FormulaCfg.inputs, FormulaCfg.rename,
      Formula.rename, naturalInputAddress, naturalConfigurationCoordinate]
  · funext v
    simp [naturalInputFormulas, NaturalFormulaCfg.restrict, FormulaCfg.inputs, FormulaCfg.rename,
      Formula.rename, naturalInputAddress, naturalConfigurationCoordinate]
  · funext k i a
    simp [naturalInputFormulas, NaturalFormulaCfg.restrict, FormulaCfg.inputs, FormulaCfg.rename,
      Formula.rename, naturalInputAddress, naturalConfigurationCoordinate]

/-- The natural-address tick is exactly the established bounded tick with renamed inputs. -/
theorem naturalTickFormulas_inputs (tm : Turing.FinTM2) (capacity : Nat) :
    (naturalTickFormulas capacity (naturalInputFormulas tm)).restrict capacity =
      (tickFormulas (FormulaCfg.inputs tm capacity)).rename (naturalInputAddress tm capacity) := by
  rw [naturalTickFormulas_restrict, naturalInputFormulas_restrict, tickFormulas_rename]

end ShiReversibleTM
