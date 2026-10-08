import ReversibleTickSymbolRowFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleFormula

theorem Formula.inputList_rename {ι κ : Type} (p : Formula ι) (f : ι → κ) :
    (p.rename f).inputList = p.inputList.map f := by
  induction p with
  | constant b => rfl
  | input i => rfl
  | neg p ih => exact ih
  | conj p q ihp ihq => simp [Formula.rename, Formula.inputList, ihp, ihq, List.map_append]

end ShiReversibleFormula
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem boundedTickFormulaForKind_size (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity)
    (kind : TickTreeKind tm) : (boundedTickFormulaForKind tm capacity i kind).size ≤ tickSizeBound tm := by
  have h := tickFormulas_size tm capacity
  cases kind with
  | inl z => cases z with
    | inl l => exact h.2.1 l
    | inr v => exact h.2.2.1 v
  | inr z => exact h.2.2.2 z.1 i z.2

theorem tickTreeForKind_selected_size (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity)
    (kind : TickTreeKind tm) :
    ((tickTreeForKind tm kind).eval (TickIndexGuard.eval capacity i.val)).size ≤ tickSizeBound tm := by
  have h := congrArg Formula.size (tickTreeForKind_formula_agreement tm capacity i kind)
  simp only [DecisionTree.evaluate, Formula.rename_size] at h
  rw [h]
  exact boundedTickFormulaForKind_size tm capacity i kind

/-- Selected symbolic inputs are genuine bounded-configuration input wires, even when other leaves query padding. -/
theorem tickTreeForKind_selected_input_address (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity)
    (kind : TickTreeKind tm) (c : TickSymbolicCoordinate tm)
    (hc : c ∈ ((tickTreeForKind tm kind).eval (TickIndexGuard.eval capacity i.val)).inputList) :
    naturalConfigurationAddress tm capacity (tickSymbolicCoordinateEval capacity i.val c) < configurationWidth tm capacity := by
  let p := (tickTreeForKind tm kind).eval (TickIndexGuard.eval capacity i.val)
  have hm : tickSymbolicCoordinateEval capacity i.val c ∈
      (p.rename (tickSymbolicCoordinateEval capacity i.val)).inputList := by
    rw [Formula.inputList_rename]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  have he : p.rename (tickSymbolicCoordinateEval capacity i.val) =
      (boundedTickFormulaForKind tm capacity i kind).rename (naturalInputAddress tm capacity) :=
    tickTreeForKind_formula_agreement tm capacity i kind
  rw [he, Formula.inputList_rename] at hm
  obtain ⟨j, hj, hcoord⟩ := List.mem_map.mp hm
  rw [← hcoord, naturalInputAddress_value]
  exact j.isLt

end ShiReversibleGenerator
