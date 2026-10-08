import ReversibleSharedEmitterPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem leafInputBudget_append {tm : Turing.FinTM2} (xs ys : List (Formula (TickSymbolicCoordinate tm))) :
    leafInputBudget (xs ++ ys) = leafInputBudget xs + leafInputBudget ys := by
  induction xs with
  | nil => simp [leafInputBudget]
  | cons p ps ih => simp [leafInputBudget, ih, Nat.add_assoc]

def traversalReserveFormula (tm : Turing.FinTM2) : Nat → Formula (TickSymbolicCoordinate tm)
  | 0 => .constant false
  | n + 1 => .conj (.input (.inl (.inl none))) (traversalReserveFormula tm n)

theorem traversalReserveFormula_inputs (tm : Turing.FinTM2) (n : Nat) :
    (traversalReserveFormula tm n).inputList.length = n := by
  induction n <;> simp_all [traversalReserveFormula, Formula.inputList]

/-- Extra dummy occurrences reserve loop metadata registers; the dummy tree is never emitted. -/
noncomputable def tickTraversalSupply (tm : Turing.FinTM2) : TickGuardFormula tm :=
  .branch ⟨.literal 0, .literal 0⟩ (machineTickSupply tm) (.leaf (traversalReserveFormula tm 8))

theorem tickTraversalSupply_budget (tm : Turing.FinTM2) :
    leafInputBudget (tickTraversalSupply tm).leaves = leafInputBudget (machineTickSupply tm).leaves + 8 := by
  simp [tickTraversalSupply, DecisionTree.leaves, leafInputBudget_append, leafInputBudget,
    traversalReserveFormula_inputs]

noncomputable def tickTraversalSpare (tm : Turing.FinTM2) (j : Fin 8) : FixedLeafRegister (tickTraversalSupply tm) :=
  .inr ⟨leafInputBudget (machineTickSupply tm).leaves + j.val, by rw [tickTraversalSupply_budget]; omega⟩

theorem tickTraversalSupply_contains (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (p : Formula (TickSymbolicCoordinate tm)) (hp : p ∈ (tickTreeForKind tm kind).leaves) :
    p ∈ (tickTraversalSupply tm).leaves := by
  have h := machineTickSupply_contains tm kind p hp
  simp [tickTraversalSupply, DecisionTree.leaves, h]

theorem tickTraversalSpare_ne_slot (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (p : Formula (TickSymbolicCoordinate tm)) (hp : p ∈ (tickTreeForKind tm kind).leaves)
    (j : Fin 8) (i : Fin p.inputList.length) :
    tickTraversalSpare tm j ≠ fixedLeafSlot (tickTraversalSupply tm) p i := by
  have h := leafInputBudget_member (machineTickSupply tm).leaves p (machineTickSupply_contains tm kind p hp)
  have hi := i.isLt
  have hb : i.val < leafInputBudget (tickTraversalSupply tm).leaves + 1 := by
    rw [tickTraversalSupply_budget]; omega
  intro he
  have hv := congrArg (fun r : FixedLeafRegister (tickTraversalSupply tm) => r.elim (fun _ => 0) Fin.val) he
  simp only [tickTraversalSpare, fixedLeafSlot, Sum.elim_inr, Nat.mod_eq_of_lt hb] at hv
  omega

end ShiReversibleGenerator
