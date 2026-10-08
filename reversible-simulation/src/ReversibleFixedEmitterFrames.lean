import ReversibleFixedGuardedEmitter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

theorem fixedLeafEmitter_control_frame (tree : TickGuardFormula tm)
    (p : Formula (TickSymbolicCoordinate tm)) (backward : Bool)
    (cs : FixedLeafRegister tree → Nat) (q : Fin 14)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9) :
    (leafPaddedCounterTemplate tm (fixedLeafBindingRegisters tree) p (fixedLeafSlot tree p)
      backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters tree)).counters cs (.inl q) = cs (.inl q) := by
  change cleanupCounters (List.ofFn (fixedLeafSlot tree p))
    (fixedNodeCounters (fixedLeafPrinterRegisters tree)
      (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨fixedLeafSlot tree p i, 0⟩)
        (.inl 12) 0 ⟨.inl 13, 0⟩)
      (coordinateBindingSequenceCounters tm (fixedLeafBindingRegisters tree)
        (leafInputBindingTasks tm p (fixedLeafSlot tree p)) cs)) (.inl q) = _
  have hn : (.inl q : FixedLeafRegister tree) ∉ List.ofFn (fixedLeafSlot tree p) := by
    simp [List.mem_ofFn, fixedLeafSlot]
  rw [cleanupCounters_apply, if_neg hn]
  rw [fixedNodeCounters_other]
  · exact fixedLeafBinding_preserves_control tree p cs q
  · simpa [fixedLeafPrinterRegisters] using hq.1
  · simpa [fixedLeafPrinterRegisters] using hq.2.1
  · simpa [fixedLeafPrinterRegisters] using hq.2.2.1
  · simpa [fixedLeafPrinterRegisters] using hq.2.2.2

theorem fixedGuardedEmitter_control_frame (tree : TickGuardFormula tm) (backward : Bool)
    (cs : FixedLeafRegister tree → Nat) (q : Fin 14)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9) :
    (fixedGuardedEmitter tree backward).counters cs (.inl q) = cs (.inl q) := by
  unfold fixedGuardedEmitter guardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  exact fixedLeafEmitter_control_frame tree _ backward cs q hq

theorem fixedGuardedEmitter_ready_preserved (tree : TickGuardFormula tm) (backward : Bool)
    (cs : FixedLeafRegister tree → Nat) (h : fixedGuardedEmitterReady tree cs) :
    fixedGuardedEmitterReady tree ((fixedGuardedEmitter tree backward).counters cs) := by
  unfold fixedGuardedEmitterReady at h ⊢
  rcases h with ⟨h3, h4, h5, h10, h11⟩
  have hframe := fixedGuardedEmitter_control_frame tree backward cs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe 3 (by decide)]; exact h3
  · rw [hframe 4 (by decide)]; exact h4
  · rw [hframe 5 (by decide)]; exact h5
  · rw [hframe 10 (by decide)]; exact h10
  · rw [hframe 11 (by decide)]; exact h11

end ShiReversibleGenerator
