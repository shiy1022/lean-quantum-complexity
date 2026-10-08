import ReversibleFixedLeafRegisters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

/-- A single fixed finite register/control program for the whole guarded formula. -/
noncomputable def fixedGuardedEmitter (tree : TickGuardFormula tm) (backward : Bool) :
    CounterProgramTemplate (FixedLeafRegister tree) :=
  guardedLeafCounterTemplate tm (fixedLeafBindingRegisters tree) (fixedLeafGuardRegisters tree)
    (fixedLeafSlot tree) backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters tree) tree

/-- Only the concrete query, guard, scratch and buffer counters need initial zero values. -/
def fixedGuardedEmitterReady (tree : TickGuardFormula tm) (cs : FixedLeafRegister tree → Nat) : Prop :=
  cs (.inl 3) = 0 ∧ cs (.inl 4) = 0 ∧ cs (.inl 5) = 0 ∧ cs (.inl 10) = 0 ∧ cs (.inl 11) = 0

theorem fixedLeafBinding_preserves_control (tree : TickGuardFormula tm)
    (p : Formula (TickSymbolicCoordinate tm)) (cs : FixedLeafRegister tree → Nat) (q : Fin 14) :
    coordinateBindingSequenceCounters tm (fixedLeafBindingRegisters tree)
      (leafInputBindingTasks tm p (fixedLeafSlot tree p)) cs (.inl q) = cs (.inl q) := by
  apply coordinateBindingSequence_preserves_other
  simp only [leafInputBindingTasks, List.forall_mem_ofFn_iff]
  intro i
  simp [fixedLeafSlot]

theorem fixedGuardedEmitter_ready (tree : TickGuardFormula tm)
    (cs : FixedLeafRegister tree → Nat) (h : fixedGuardedEmitterReady tree cs) :
    (fixedGuardedEmitter tree false).ready cs ∧ (fixedGuardedEmitter tree true).ready cs := by
  have leafReady : ∀ p backward,
      (leafPaddedCounterTemplate tm (fixedLeafBindingRegisters tree) p (fixedLeafSlot tree p)
        backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters tree)).ready cs := by
    intro p backward
    change cs (.inl 3) = 0 ∧ cs (.inl 5) = 0 ∧
      coordinateBindingSequenceCounters tm (fixedLeafBindingRegisters tree)
        (leafInputBindingTasks tm p (fixedLeafSlot tree p)) cs (.inl 10) = 0 ∧
      coordinateBindingSequenceCounters tm (fixedLeafBindingRegisters tree)
        (leafInputBindingTasks tm p (fixedLeafSlot tree p)) cs (.inl 5) = 0
    rw [fixedLeafBinding_preserves_control, fixedLeafBinding_preserves_control]
    exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.1⟩
  have treeReady : ∀ (t : TickGuardFormula tm) backward,
      (compileGuardedTree (fixedLeafGuardRegisters tree)
        (fun p => leafPaddedCounterTemplate tm (fixedLeafBindingRegisters tree) p (fixedLeafSlot tree p)
          backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters tree)) t).ready cs := by
    intro t backward
    induction t with
    | leaf p => exact leafReady p backward
    | branch g y n ihy ihn =>
      exact ⟨h.2.1, h.2.2.2.2, h.2.2.1, ihy, ihn⟩
  exact ⟨treeReady tree false, treeReady tree true⟩

theorem fixedGuardedEmitter_run (tree : TickGuardFormula tm) (backward : Bool) :
    (fixedGuardedEmitter tree backward).Runs := by
  apply guardedLeafCounterTemplate_run tm _ _ (fixedLeafGuardRegisters_valid tree) _ _ _ _ _ _ tree
    (fixedLeafPrinterRegisters_valid tree)
  · simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters]
  · simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters]
  · intro p hp i; exact fixedLeafSlot_valid tree p i
  · intro p hp i; exact fixedLeafSlot_source_stable tree p i

theorem fixedGuardedEmitter_polynomial (tree : TickGuardFormula tm) (backward : Bool)
    (bound : Polynomial Nat) : (fixedGuardedEmitter tree backward).PolynomiallyTimed bound := by
  apply guardedLeafCounterTemplate_polynomial tm _ _ (fixedLeafGuardRegisters_valid tree)
    _ _ _ _ _ _ tree _ bound
  intro p hp i; exact fixedLeafSlot_valid tree p i

end ShiReversibleGenerator
