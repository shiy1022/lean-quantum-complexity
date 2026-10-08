import ReversibleStridedGuardedLeafCompiler
import ReversibleFixedGuardedEmitter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

theorem stridedFixedLeafBinding_preserves_control (tree : TickGuardFormula tm) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (cs : FixedLeafRegister tree → Nat) (q : Fin 14) :
    stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters tree) inputStride
      (leafInputBindingTasks tm p (fixedLeafSlot tree p)) cs (.inl q) = cs (.inl q) := by
  apply stridedCoordinateBindingSequence_preserves_other
  simp only [leafInputBindingTasks, List.forall_mem_ofFn_iff]
  intro i
  simp [fixedLeafSlot]

/-- A single fixed finite register/control program for the whole guarded formula. -/
noncomputable def stridedSharedFixedGuardedEmitter (supply tree : TickGuardFormula tm) (inputStride : Nat) (backward : Bool) :
    CounterProgramTemplate (FixedLeafRegister supply) :=
  stridedGuardedLeafCounterTemplate tm (fixedLeafBindingRegisters supply) inputStride (fixedLeafGuardRegisters supply)
    (fixedLeafSlot supply) backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply) tree

theorem stridedSharedFixedGuardedEmitter_ready (supply tree : TickGuardFormula tm) (inputStride : Nat)
    (cs : FixedLeafRegister supply → Nat) (h : fixedGuardedEmitterReady supply cs) :
    (stridedSharedFixedGuardedEmitter supply tree inputStride false).ready cs ∧ (stridedSharedFixedGuardedEmitter supply tree inputStride true).ready cs := by
  have leafReady : ∀ p backward,
      (stridedLeafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) inputStride p (fixedLeafSlot supply p)
        backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)).ready cs := by
    intro p backward
    change cs (.inl 3) = 0 ∧ cs (.inl 5) = 0 ∧
      stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply) inputStride
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs (.inl 10) = 0 ∧
      stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply) inputStride
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs (.inl 5) = 0
    rw [stridedFixedLeafBinding_preserves_control, stridedFixedLeafBinding_preserves_control]
    exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.1⟩
  have treeReady : ∀ (t : TickGuardFormula tm) backward,
      (compileGuardedTree (fixedLeafGuardRegisters supply)
        (fun p => stridedLeafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) inputStride p (fixedLeafSlot supply p)
          backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)) t).ready cs := by
    intro t backward
    induction t with
    | leaf p => exact leafReady p backward
    | branch g y n ihy ihn =>
      exact ⟨h.2.1, h.2.2.2.2, h.2.2.1, ihy, ihn⟩
  exact ⟨treeReady tree false, treeReady tree true⟩

theorem stridedSharedFixedGuardedEmitter_run (supply tree : TickGuardFormula tm) (inputStride : Nat) (backward : Bool) :
    (stridedSharedFixedGuardedEmitter supply tree inputStride backward).Runs := by
  apply stridedGuardedLeafCounterTemplate_run tm _ inputStride _ (fixedLeafGuardRegisters_valid supply) _ _ _ _ _ _ tree
    (fixedLeafPrinterRegisters_valid supply)
  · simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters]
  · simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters]
  · intro p hp i; exact fixedLeafSlot_valid supply p i
  · intro p hp i; exact fixedLeafSlot_source_stable supply p i

theorem stridedSharedFixedGuardedEmitter_polynomial (supply tree : TickGuardFormula tm) (inputStride : Nat) (backward : Bool)
    (bound : Polynomial Nat) : (stridedSharedFixedGuardedEmitter supply tree inputStride backward).PolynomiallyTimed bound := by
  apply stridedGuardedLeafCounterTemplate_polynomial tm _ inputStride _ (fixedLeafGuardRegisters_valid supply)
    _ _ _ _ _ _ tree _ bound
  intro p hp i; exact fixedLeafSlot_valid supply p i


end ShiReversibleGenerator
