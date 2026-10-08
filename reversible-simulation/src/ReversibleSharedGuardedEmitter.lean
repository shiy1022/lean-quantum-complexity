import ReversibleGuardedTickRelocation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

/-- A single fixed finite register/control program for the whole guarded formula. -/
noncomputable def sharedFixedGuardedEmitter (supply tree : TickGuardFormula tm) (backward : Bool) :
    CounterProgramTemplate (FixedLeafRegister supply) :=
  guardedLeafCounterTemplate tm (fixedLeafBindingRegisters supply) (fixedLeafGuardRegisters supply)
    (fixedLeafSlot supply) backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply) tree

theorem sharedFixedGuardedEmitter_ready (supply tree : TickGuardFormula tm)
    (cs : FixedLeafRegister supply → Nat) (h : fixedGuardedEmitterReady supply cs) :
    (sharedFixedGuardedEmitter supply tree false).ready cs ∧ (sharedFixedGuardedEmitter supply tree true).ready cs := by
  have leafReady : ∀ p backward,
      (leafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) p (fixedLeafSlot supply p)
        backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)).ready cs := by
    intro p backward
    change cs (.inl 3) = 0 ∧ cs (.inl 5) = 0 ∧
      coordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply)
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs (.inl 10) = 0 ∧
      coordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply)
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs (.inl 5) = 0
    rw [fixedLeafBinding_preserves_control, fixedLeafBinding_preserves_control]
    exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.1⟩
  have treeReady : ∀ (t : TickGuardFormula tm) backward,
      (compileGuardedTree (fixedLeafGuardRegisters supply)
        (fun p => leafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) p (fixedLeafSlot supply p)
          backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)) t).ready cs := by
    intro t backward
    induction t with
    | leaf p => exact leafReady p backward
    | branch g y n ihy ihn =>
      exact ⟨h.2.1, h.2.2.2.2, h.2.2.1, ihy, ihn⟩
  exact ⟨treeReady tree false, treeReady tree true⟩

theorem sharedFixedGuardedEmitter_run (supply tree : TickGuardFormula tm) (backward : Bool) :
    (sharedFixedGuardedEmitter supply tree backward).Runs := by
  apply guardedLeafCounterTemplate_run tm _ _ (fixedLeafGuardRegisters_valid supply) _ _ _ _ _ _ tree
    (fixedLeafPrinterRegisters_valid supply)
  · simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters]
  · simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters]
  · intro p hp i; exact fixedLeafSlot_valid supply p i
  · intro p hp i; exact fixedLeafSlot_source_stable supply p i

theorem sharedFixedGuardedEmitter_polynomial (supply tree : TickGuardFormula tm) (backward : Bool)
    (bound : Polynomial Nat) : (sharedFixedGuardedEmitter supply tree backward).PolynomiallyTimed bound := by
  apply guardedLeafCounterTemplate_polynomial tm _ _ (fixedLeafGuardRegisters_valid supply)
    _ _ _ _ _ _ tree _ bound
  intro p hp i; exact fixedLeafSlot_valid supply p i

theorem sharedFixedGuardedEmitter_control_frame (supply tree : TickGuardFormula tm) (backward : Bool)
    (cs : FixedLeafRegister supply → Nat) (q : Fin 14)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9) :
    (sharedFixedGuardedEmitter supply tree backward).counters cs (.inl q) = cs (.inl q) := by
  unfold sharedFixedGuardedEmitter guardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  exact fixedLeafEmitter_control_frame supply _ backward cs q hq

end ShiReversibleGenerator
