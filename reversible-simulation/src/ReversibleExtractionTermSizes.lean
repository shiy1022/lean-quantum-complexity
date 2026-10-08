import ReversibleExtractionDisjoinCompiler
import ReversibleMachineExtraction

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversibleFormula

/-- Each empty-marker query reads one configuration bit, including the virtual endpoint. -/
theorem extraction_emptySlot_size (tm : Turing.FinTM2) (capacity ell : Nat) :
    (emptySlot (extractionEmpty tm capacity) ell).size=1 := by
  unfold emptySlot
  split <;> simp [extractionEmpty,FormulaCfg.inputs,Formula.size]

/-- The finite symbol table has an exact capacity-independent compiler size. -/
theorem extractionPayload_size_exact (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity : Nat) (i : Fin capacity) :
    (extractionPayload tm e capacity i).size=1+Fintype.card (Option (MachineSymbol tm))*7 := by
  classical
  let term := fun a : Option (MachineSymbol tm) =>
    Formula.conj (Formula.constant (decide (outputCellBool e a=true)))
      ((FormulaCfg.inputs tm capacity).cells tm.k₁ i a)
  have h : ∀ xs : List (Option (MachineSymbol tm)),(disjoin (xs.map term)).size=1+xs.length*7 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.map_cons,disjoin,List.foldr_cons,Formula.size_disj]
      change (term a).size+(disjoin (xs.map term)).size+4=_
      rw [ih]
      simp [term,FormulaCfg.inputs,Formula.size,Nat.succ_mul]
      omega
  unfold extractionPayload unaryTable
  simpa only [Finset.length_toList,Finset.card_univ] using h Finset.univ.toList

/-- Both runtime branch tests are explicit in the exact output-value size. -/
theorem extraction_outputValue_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) :
    (outputValue (extractionPayload tm e capacity) ell j).size=
      1+(if ell+1 ≤ j ∧ j < 2*ell+1 ∧ j-ell-1 < capacity then
        Fintype.card (Option (MachineSymbol tm))*7 else 0) := by
  by_cases hfirst : j < ell
  · have hnot : ¬(ell+1 ≤ j ∧ j < 2*ell+1 ∧ j-ell-1 < capacity) := by omega
    simp [outputValue,hfirst,hnot,Formula.size]
    omega
  · unfold outputValue
    simp only [if_neg hfirst]
    split <;> simp_all [extractionPayload_size_exact,Formula.size]

/-- Exact selected-term size, suitable for a finite suffix-size pass over ell. -/
theorem extraction_selectedTerm_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) :
    (Formula.conj (lengthFlag (extractionEmpty tm capacity) ell)
      (outputValue (extractionPayload tm e capacity) ell j)).size=
      (if ell=0 then 5 else 6)+
        (if ell+1 ≤ j ∧ j < 2*ell+1 ∧ j-ell-1 < capacity then
          Fintype.card (Option (MachineSymbol tm))*7 else 0) := by
  rw [Formula.size,extraction_outputValue_size]
  unfold lengthFlag
  by_cases h : ell=0 <;>
    simp [h,Formula.size,extraction_emptySlot_size] <;> omega

end ShiReversibleTM
