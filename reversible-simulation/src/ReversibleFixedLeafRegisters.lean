import ReversibleGuardedLeafCompiler

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

def leafInputBudget : List (Formula (TickSymbolicCoordinate tm)) → Nat
  | [] => 0
  | p :: ps => p.inputList.length + leafInputBudget ps

theorem leafInputBudget_member (ps : List (Formula (TickSymbolicCoordinate tm)))
    (p : Formula (TickSymbolicCoordinate tm)) (hp : p ∈ ps) : p.inputList.length ≤ leafInputBudget ps := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with h | h
    · subst p; simp only [leafInputBudget]; omega
    · have h' := ih h
      simp only [leafInputBudget]; omega

abbrev FixedLeafRegister (tree : TickGuardFormula tm) := Fin 14 ⊕ Fin (leafInputBudget tree.leaves + 1)

def fixedLeafSlot (tree : TickGuardFormula tm) (p : Formula (TickSymbolicCoordinate tm))
    (i : Fin p.inputList.length) : FixedLeafRegister tree :=
  .inr ⟨i.val % (leafInputBudget tree.leaves + 1), Nat.mod_lt _ (by omega)⟩

theorem fixedLeafSlot_injective (tree : TickGuardFormula tm) (p : Formula (TickSymbolicCoordinate tm))
    (hp : p ∈ tree.leaves) : Function.Injective (fixedLeafSlot tree p) := by
  intro i j he
  have hb := leafInputBudget_member tree.leaves p hp
  have hi : i.val < leafInputBudget tree.leaves + 1 := by omega
  have hj : j.val < leafInputBudget tree.leaves + 1 := by omega
  have hv := congrArg (fun r : FixedLeafRegister tree => r.elim (fun _ => 0) Fin.val) he
  simp only [fixedLeafSlot, Sum.elim_inr, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  exact Fin.ext hv

def fixedLeafBindingRegisters (tree : TickGuardFormula tm) : CoordinateBindingRegisters (FixedLeafRegister tree) :=
  ⟨.inl 0, .inl 1, .inl 2, .inl 3, .inl 4, .inl 5⟩

def fixedLeafPrinterRegisters (tree : TickGuardFormula tm) : NodePrinterRegisters (FixedLeafRegister tree) :=
  ⟨.inl 6, .inl 7, .inl 8, .inl 9, .inl 10, .inl 5⟩

def fixedLeafGuardRegisters (tree : TickGuardFormula tm) : GuardProgramRegisters (FixedLeafRegister tree) :=
  ⟨.inl 1, .inl 2, .inl 4, .inl 11, .inl 5⟩

theorem fixedLeafSlot_valid (tree : TickGuardFormula tm) (p : Formula (TickSymbolicCoordinate tm))
    (i : Fin p.inputList.length) :
    ((fixedLeafBindingRegisters tree).withTarget (fixedLeafSlot tree p i)).Valid := by
  constructor <;> simp [fixedLeafBindingRegisters, CoordinateBindingRegisters.withTarget, fixedLeafSlot]

theorem fixedLeafSlot_source_stable (tree : TickGuardFormula tm) (p : Formula (TickSymbolicCoordinate tm))
    (i : Fin p.inputList.length) : (fixedLeafPrinterRegisters tree).SourceStable (fixedLeafSlot tree p i) := by
  simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters, fixedLeafSlot]

theorem fixedLeafPrinterRegisters_valid (tree : TickGuardFormula tm) :
    (fixedLeafPrinterRegisters tree).Valid := by
  simp [NodePrinterRegisters.Valid, fixedLeafPrinterRegisters]

theorem fixedLeafGuardRegisters_valid (tree : TickGuardFormula tm) :
    (fixedLeafGuardRegisters tree).Valid := by
  constructor <;> simp [fixedLeafGuardRegisters]

end ShiReversibleGenerator
