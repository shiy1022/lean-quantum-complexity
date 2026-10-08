import ReversibleExtractionSizeContribution
import ReversibleFormulaRenaming
import ReversibleNaturalTickInputs

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

inductive ExtractionValueKind where
  | zero | one | payload
  deriving DecidableEq

abbrev ExtractionTermInput (tm : Turing.FinTM2) := Fin 2 ⊕ Option (MachineSymbol tm)

/-- One of finitely many term schemas. Runtime indices occur only in the input-address bindings. -/
noncomputable def extractionTermSchema (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (first endpoint : Bool) (value : ExtractionValueKind) : Formula (ExtractionTermInput tm) :=
  .conj (.conj (if first then .constant true else .neg (.input (.inl 0)))
    (if endpoint then .constant true else .input (.inl 1)))
    (match value with
      | .zero => .constant false
      | .one => .constant true
      | .payload => unaryTable (outputCellBool e) (fun a => .input (.inr a)) true)

/-- The concrete addresses for predecessor/current empty markers and the selected payload cell. -/
def extractionTermNaturalInput (tm : Turing.FinTM2) (ell j : Nat) : ExtractionTermInput tm → NaturalConfigurationBit tm
  | .inl i => .inr ((tm.k₁,if i.val=0 then ell-1 else ell),none)
  | .inr a => .inr ((tm.k₁,j-ell-1),a)

noncomputable def extractionRuntimeValueKind (ell j : Nat) : ExtractionValueKind :=
  if j < ell then .one else if ell+1 ≤ j ∧ j ≤ 2*ell then .payload else .zero

/-- Exact agreement of the finite term schema with the original selected output formula. -/
theorem extractionTermSchema_agreement (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) (hell : ell ≤ capacity) :
    (extractionTermSchema tm e (decide (ell=0)) (decide (capacity ≤ ell))
      (extractionRuntimeValueKind ell j)).rename (extractionTermNaturalInput tm ell j)=
    (Formula.conj (lengthFlag (extractionEmpty tm capacity) ell)
      (outputValue (extractionPayload tm e capacity) ell j)).rename (naturalInputAddress tm capacity) := by
  classical
  have hvalid : (ell+1 ≤ j ∧ j < 2*ell+1 ∧ j-ell-1 < capacity) ↔ (ell+1 ≤ j ∧ j ≤ 2*ell) := by omega
  by_cases hz : ell=0
  · subst ell
    have hv : ¬(1 ≤ j ∧ j ≤ 0) := by omega
    have hv' : ¬(1 ≤ j ∧ j < 1 ∧ j-0-1 < capacity) := by omega
    by_cases hc : 0 < capacity
    all_goals simp [extractionTermSchema,extractionRuntimeValueKind,extractionTermNaturalInput,
      lengthFlag,emptySlot,outputValue,extractionEmpty,extractionPayload,FormulaCfg.inputs,
      Formula.rename,naturalInputAddress,naturalConfigurationCoordinate,hc,hv,hv']
    all_goals split_ifs <;> simp_all [Formula.rename,extractionTermNaturalInput,naturalInputAddress,naturalConfigurationCoordinate,rename_unaryTable]
    all_goals omega
  · have hp : ell-1 < capacity := by omega
    by_cases hc : ell < capacity <;>
      by_cases hf : j < ell <;>
      by_cases hv : ell+1 ≤ j ∧ j ≤ 2*ell
    all_goals simp [extractionTermSchema,extractionRuntimeValueKind,extractionTermNaturalInput,
      lengthFlag,emptySlot,outputValue,extractionEmpty,extractionPayload,FormulaCfg.inputs,
      Formula.rename,naturalInputAddress,naturalConfigurationCoordinate,hz,hp,hc,hf,hv,
      hvalid,show capacity ≤ ell ↔ ¬ell < capacity by omega,rename_unaryTable]
    all_goals split_ifs <;> simp_all [Formula.rename,extractionTermNaturalInput,naturalInputAddress,naturalConfigurationCoordinate,rename_unaryTable]
    all_goals omega

end ShiReversibleGenerator
