import ReversibleTickCoordinateFieldBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

/-- Binding slots are erased and every other private counter is preserved. -/
theorem stridedFixedLeafEmitter_private_le (supply : TickGuardFormula tm) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (backward : Bool)
    (cs : FixedLeafRegister supply → Nat) (j : Fin (leafInputBudget supply.leaves + 1)) :
    (stridedLeafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) inputStride p
      (fixedLeafSlot supply p) backward (.inl 12) 0 ⟨.inl 13, 0⟩
      (fixedLeafPrinterRegisters supply)).counters cs (.inr j) ≤ cs (.inr j) := by
  change cleanupCounters (List.ofFn (fixedLeafSlot supply p))
    (fixedNodeCounters (fixedLeafPrinterRegisters supply)
      (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨fixedLeafSlot supply p i, 0⟩)
        (.inl 12) 0 ⟨.inl 13, 0⟩)
      (stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply) inputStride
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs)) (.inr j) ≤ _
  rw [cleanupCounters_apply]
  split
  · exact Nat.zero_le _
  · rename_i hn
    rw [fixedNodeCounters_other]
    · rw [stridedCoordinateBindingSequence_preserves_other]
      simp only [leafInputBindingTasks, List.forall_mem_ofFn_iff]
      intro i he
      exact hn (List.mem_ofFn.mpr ⟨i, he.symm⟩)
    all_goals simp [fixedLeafPrinterRegisters]

theorem stridedSharedFixedGuardedEmitter_private_le (supply tree : TickGuardFormula tm)
    (inputStride : Nat) (backward : Bool) (cs : FixedLeafRegister supply → Nat)
    (j : Fin (leafInputBudget supply.leaves + 1)) :
    (stridedSharedFixedGuardedEmitter supply tree inputStride backward).counters cs (.inr j) ≤ cs (.inr j) := by
  unfold stridedSharedFixedGuardedEmitter stridedGuardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  exact stridedFixedLeafEmitter_private_le supply inputStride _ backward cs j

theorem stridedTickCoordinateBody_private_le (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (j : Fin (leafInputBudget (tickTraversalSupply tm).leaves + 1)) :
    (stridedTickCoordinateBody tm kind inputStride strideBound backward).counters cs (.inr j) ≤ cs (.inr j) := by
  change (stridedSharedFixedGuardedEmitter (tickTraversalSupply tm) (tickTreeForKind tm kind)
    inputStride backward).counters (tickOutputPreparationCounters tm kind strideBound cs) (.inr j) ≤ _
  have h := stridedSharedFixedGuardedEmitter_private_le (tickTraversalSupply tm) (tickTreeForKind tm kind)
    inputStride backward (tickOutputPreparationCounters tm kind strideBound cs) j
  simpa [tickOutputPreparationCounters] using h

end ShiReversibleGenerator
