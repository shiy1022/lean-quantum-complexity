import ReversibleFormulaRenaming
import ReversibleInitialization

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

noncomputable def initializationInputCellSchema (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) : Formula Unit := by
  classical
  exact unaryTable (fun b => some (inputSymbol tm (e.symm b)))
    (fun b => if b then .input () else .neg (.input ())) a

/-- The only dynamic input coordinate is supplied by renaming one fixed formula. -/
theorem initializationInputCellSchema_specialize (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) {n : Nat} (i : Fin n) :
    (initializationInputCellSchema tm e a).rename (fun _ => i) =
      unaryTable (fun b => some (inputSymbol tm (e.symm b))) (booleanInputCodes i) a := by
  classical
  unfold initializationInputCellSchema
  rw [rename_unaryTable]
  congr 1
  funext b
  cases b <;> rfl

theorem initializationInputCellSchema_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) : (initializationInputCellSchema tm e a).size ≤ 17 := by
  have h := booleanInputCodes_size (0 : Fin 1)
  have hs := initializationInputCellSchema_specialize tm e a (0 : Fin 1)
  have hr := Formula.rename_size (initializationInputCellSchema tm e a) (fun _ : Unit => (0 : Fin 1))
  classical
  have ht := size_unaryTable (fun b => some (inputSymbol tm (e.symm b)))
    (booleanInputCodes (0 : Fin 1)) a 2 h
  rw [← hs, hr] at ht
  simpa using ht

theorem initialFormulas_input_cell_schema (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (hi : i.val < n) (a : Option (MachineSymbol tm)) :
    (initialFormulas tm e capacity n).cells tm.k₀ i a =
      (initializationInputCellSchema tm e a).rename (fun _ => (⟨i.val, hi⟩ : Fin n)) := by
  classical
  rw [initializationInputCellSchema_specialize]
  simp [initialFormulas, hi]
  congr 1

theorem initialFormulas_padding_cell_schema (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm))
    (h : k ≠ tm.k₀ ∨ n ≤ i.val) :
    (initialFormulas tm e capacity n).cells k i a = .constant (oneHot none a) := by
  classical
  rcases h with hk | hi
  · simp [initialFormulas, hk]
    unfold oneHot
    congr 1 <;> exact Subsingleton.elim _ _
  · simp [initialFormulas, not_lt.mpr hi]
    unfold oneHot
    congr 1 <;> exact Subsingleton.elim _ _

/-- Raw initialization compiler agrees with the fixed schema plus the runtime wire address. -/
theorem initializationInputCellSchema_rawCompile (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (hi : i.val < n) (a : Option (MachineSymbol tm))
    (inputs : Fin n → Nat) (base : Nat) :
    ((initialFormulas tm e capacity n).cells tm.k₀ i a).rawCompile inputs base =
      (initializationInputCellSchema tm e a).rawCompile
        (fun _ => inputs ⟨i.val, hi⟩) base := by
  rw [initialFormulas_input_cell_schema, Formula.rename_rawCompile]

end ShiReversibleGenerator
