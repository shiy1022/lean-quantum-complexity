import ReversibleInitializationExactLayers
import ReversibleConstantCoordinateSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

theorem constantSequence_exact_layers (header stackRank symbolCard : Nat) (backward : Bool)
    (ars : List (Bool × Nat)) (cs : InitializationRegister → Nat) :
    constantSequenceCounters header stackRank symbolCard backward ars cs (.inr 10) =
      cs (.inr 10) + (ars.map (fun ar =>
        formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum := by
  induction ars generalizing cs with
  | nil => simp [constantSequenceCounters]
  | cons ar ars ih =>
    rw [constantSequenceCounters, ih, locatedConstant_exact_layers]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem symbolSequence_exact_layers (header stackRank symbolCard : Nat) (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))
    (cs : InitializationRegister → Nat) :
    symbolSequenceCounters header stackRank symbolCard tm e backward ars cs (.inr 10) =
      cs (.inr 10) + (ars.map (fun ar =>
        (if cs (.inr 0) < cs (.inl 0) then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
         else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum := by
  induction ars generalizing cs with
  | nil => simp [symbolSequenceCounters]
  | cons ar ars ih =>
    rw [symbolSequenceCounters, ih, locatedInitialization_exact_layers]
    simp only [locatedInitialization_preserves_index, locatedInitialization_preserves_metadata,
      List.map_cons, List.sum_cons]
    omega

theorem initialFormulas_input_cell_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (a : Option (MachineSymbol tm)) :
    formulaElementaryLayers ((initialFormulas tm e capacity n).cells tm.k₀ i a) =
      if i.val < n then formulaElementaryLayers (initializationInputCellSchema tm e a)
      else formulaElementaryLayers (.constant (oneHot none a) : Formula Unit) := by
  by_cases hi : i.val < n
  · rw [if_pos hi, initialFormulas_input_cell_schema tm e capacity n i hi a,
      formulaElementaryLayers_rename]
  · rw [if_neg hi, initialFormulas_padding_cell_schema tm e capacity n tm.k₀ i a
      (Or.inr (Nat.le_of_not_gt hi))]
    rfl

/-- Exact counted layers of the located input printer agree with its established formula coordinate. -/
theorem locatedInitialization_formula_layers (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (capacity n : Nat) (i : Fin capacity)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = i.val) :
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 10) =
      cs (.inr 10) + formulaElementaryLayers ((initialFormulas tm e capacity n).cells tm.k₀ i a) + 1 := by
  rw [locatedInitialization_exact_layers, initialFormulas_input_cell_layers, hn, hi]

end ShiReversibleGenerator
