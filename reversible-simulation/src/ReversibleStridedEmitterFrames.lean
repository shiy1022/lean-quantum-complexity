import ReversibleStridedSharedEmitterPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

theorem stridedFixedLeafEmitter_control_frame (tree : TickGuardFormula tm) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (backward : Bool)
    (cs : FixedLeafRegister tree → Nat) (q : Fin 14)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9) :
    (stridedLeafPaddedCounterTemplate tm (fixedLeafBindingRegisters tree) inputStride p (fixedLeafSlot tree p)
      backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters tree)).counters cs (.inl q) = cs (.inl q) := by
  change cleanupCounters (List.ofFn (fixedLeafSlot tree p))
    (fixedNodeCounters (fixedLeafPrinterRegisters tree)
      (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨fixedLeafSlot tree p i, 0⟩)
        (.inl 12) 0 ⟨.inl 13, 0⟩)
      (stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters tree) inputStride
        (leafInputBindingTasks tm p (fixedLeafSlot tree p)) cs)) (.inl q) = _
  have hn : (.inl q : FixedLeafRegister tree) ∉ List.ofFn (fixedLeafSlot tree p) := by
    simp [List.mem_ofFn, fixedLeafSlot]
  rw [cleanupCounters_apply, if_neg hn]
  rw [fixedNodeCounters_other]
  · exact stridedFixedLeafBinding_preserves_control tree inputStride p cs q
  · simpa [fixedLeafPrinterRegisters] using hq.1
  · simpa [fixedLeafPrinterRegisters] using hq.2.1
  · simpa [fixedLeafPrinterRegisters] using hq.2.2.1
  · simpa [fixedLeafPrinterRegisters] using hq.2.2.2

theorem stridedSharedFixedGuardedEmitter_control_frame (supply tree : TickGuardFormula tm)
    (inputStride : Nat) (backward : Bool) (cs : FixedLeafRegister supply → Nat) (q : Fin 14)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9) :
    (stridedSharedFixedGuardedEmitter supply tree inputStride backward).counters cs (.inl q) = cs (.inl q) := by
  unfold stridedSharedFixedGuardedEmitter stridedGuardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  exact stridedFixedLeafEmitter_control_frame supply inputStride _ backward cs q hq

end ShiReversibleGenerator
