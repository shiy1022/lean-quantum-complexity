import ReversibleOutputFormulas
import ReversibleFormulaConfiguration
import ReversibleForestCircuit

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversibleCoding ShiReversibleFormula

noncomputable def outputCellBool {tm : Turing.FinTM2} (e : tm.Γ tm.k₁ ≃ Bool)
    (a : Option (MachineSymbol tm)) : Bool :=
  ((decodeCellSymbol tm.k₁ a).map e).getD false

theorem BoundedCfg.cell_decode {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) (i : Fin capacity) :
    decodeCellSymbol k (c.encode.cells k i) = (c.cfg.stk k)[i.val]? := by
  simp only [BoundedCfg.encode, tapeEncode, BoundedCfg.stackSymbols, List.getElem?_map]
  have hop (z : Option {a : tm.Γ k // a ∈ c.cfg.stk k}) :
      decodeCellSymbol k (z.map (fun a =>
        (⟨⟨k, a.val⟩, c.alphabet k a.val a.property⟩ : MachineSymbol tm))) =
      z.map Subtype.val := by
    cases z <;> simp [decodeCellSymbol]
  rw [hop]
  exact (List.getElem?_map).symm.trans
    (congrArg (fun xs => xs[i.val]?) (List.attach_map_subtype_val (c.cfg.stk k)))

theorem BoundedCfg.cell_empty {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (k : tm.K) (i : Fin capacity) :
    (c.encode.cells k i = none) ↔ (c.cfg.stk k)[i.val]? = none := by
  simp only [BoundedCfg.encode, tapeEncode, List.getElem?_eq_none_iff,
    BoundedCfg.stackSymbols_length]

noncomputable def extractionEmpty (tm : Turing.FinTM2) (capacity : Nat) :
    Fin capacity → Formula (Fin (configurationWidth tm capacity)) :=
  fun i => (FormulaCfg.inputs tm capacity).cells tm.k₁ i none

noncomputable def extractionPayload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity : Nat) : Fin capacity → Formula (Fin (configurationWidth tm capacity)) := by
  classical
  exact fun i => unaryTable (outputCellBool e) ((FormulaCfg.inputs tm capacity).cells tm.k₁ i) true

theorem extractionEmpty_eval {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (e : tm.Γ tm.k₁ ≃ Bool) (i : Fin capacity) :
    (extractionEmpty tm capacity i).eval c.encode.bitEncode =
      decide (((c.cfg.stk tm.k₁).map e)[i.val]? = none) := by
  classical
  have h := (FormulaCfg.inputs_denotes c.encode).2.2 tm.k₁ i none
  simpa [extractionEmpty, oneHot, BoundedCfg.cell_empty, List.getElem?_eq_none_iff] using h

theorem extractionPayload_eval {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (e : tm.Γ tm.k₁ ≃ Bool) (i : Fin capacity) :
    (extractionPayload tm e capacity i).eval c.encode.bitEncode =
      (((c.cfg.stk tm.k₁).map e)[i.val]?).getD false := by
  classical
  have h := eval_unaryTable (outputCellBool e)
    ((FormulaCfg.inputs tm capacity).cells tm.k₁ i) c.encode.bitEncode
    (c.encode.cells tm.k₁ i) true ((FormulaCfg.inputs_denotes c.encode).2.2 tm.k₁ i)
  simpa [extractionPayload, oneHot, outputCellBool, BoundedCfg.cell_decode,
    List.getElem?_map] using h

noncomputable def extractionFormula (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j : Nat) : Formula (Fin (configurationWidth tm capacity)) :=
  outputFormula (extractionEmpty tm capacity) (extractionPayload tm e capacity) j

theorem extractionFormula_eval {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (e : tm.Γ tm.k₁ ≃ Bool) (j : Nat) :
    (extractionFormula tm e capacity j).eval c.encode.bitEncode =
      (ShiReversible.outputCode capacity ((c.cfg.stk tm.k₁).map e))[j]?.getD false := by
  rw [outputCode_bit]
  exact outputFormula_eval _ _ _ _ (by simpa using c.length_bound tm.k₁)
    (extractionEmpty_eval c e) (extractionPayload_eval c e) j

noncomputable def extractionBitBound (tm : Turing.FinTM2) (capacity : Nat) : Nat := by
  classical
  exact 1 + (capacity + 1) * (10 + Fintype.card (Option (MachineSymbol tm)) * 7)

theorem extractionFormula_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity j : Nat) : (extractionFormula tm e capacity j).size ≤ extractionBitBound tm capacity := by
  classical
  have hp : ∀ i, (extractionPayload tm e capacity i).size ≤
      1 + Fintype.card (Option (MachineSymbol tm)) * 7 := by
    intro i
    exact size_unaryTable _ _ true 1 (fun a => by rfl)
  have h := outputFormula_size (extractionEmpty tm capacity) (extractionPayload tm e capacity)
    1 (1 + Fintype.card (Option (MachineSymbol tm)) * 7) (by omega) (by omega)
    (fun i => by rfl) hp j
  convert h using 1 <;> simp only [extractionFormula, extractionBitBound] <;> ring

noncomputable def extractionForest (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity : Nat) : List (Formula (Fin (configurationWidth tm capacity))) :=
  List.ofFn (fun j : Fin (2 * capacity + 1) => extractionFormula tm e capacity j.val)

@[simp] theorem extractionForest_length (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity : Nat) : (extractionForest tm e capacity).length = 2 * capacity + 1 := by
  simp [extractionForest]

theorem extractionForest_eval {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (e : tm.Γ tm.k₁ ≃ Bool)
    (j : Fin (extractionForest tm e capacity).length) :
    ((extractionForest tm e capacity)[j.val]).eval c.encode.bitEncode =
      (ShiReversible.outputCode capacity ((c.cfg.stk tm.k₁).map e))[j.val]?.getD false := by
  simp only [extractionForest, List.getElem_ofFn]
  exact extractionFormula_eval c e j.val

theorem extractionForest_size (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity : Nat) : ∀ p ∈ extractionForest tm e capacity, p.size ≤ extractionBitBound tm capacity := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact extractionFormula_size tm e capacity i.val

theorem extractionForest_workspace (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity : Nat) : forestSize (extractionForest tm e capacity) ≤
      (2 * capacity + 1) * extractionBitBound tm capacity := by
  simpa using forestSize_bound _ _ (extractionForest_size tm e capacity)

theorem extractionCircuit_output {tm : Turing.FinTM2} {capacity : Nat}
    (c : BoundedCfg tm capacity) (e : tm.Γ tm.k₁ ≃ Bool) :
    List.ofFn ((forestCircuit (extractionForest tm e capacity)).eval c.encode.bitEncode) =
      ShiReversible.outputCode capacity ((c.cfg.stk tm.k₁).map e) := by
  have hw := ShiReversible.outputCode_width capacity ((c.cfg.stk tm.k₁).map e)
    (by simpa using c.length_bound tm.k₁)
  apply List.ext_getElem
  · simp [hw]
  · intro j hj hk
    rw [List.getElem_ofFn, forestCircuit_eval, extractionForest_eval]
    simp [List.getElem?_eq_getElem hk]

end ShiReversibleTM
