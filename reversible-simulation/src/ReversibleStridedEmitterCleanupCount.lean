import ReversibleStridedEmitterFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

theorem stridedFixedLeafEmitter_count (supply : TickGuardFormula tm) (inputStride : Nat) (p : Formula (TickSymbolicCoordinate tm))
    (backward : Bool) (cs : FixedLeafRegister supply → Nat) :
    (stridedLeafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) inputStride p (fixedLeafSlot supply p)
      backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)).counters cs (.inl 9) =
      cs (.inl 9) + formulaElementaryLayers p + 1 := by
  change cleanupCounters (List.ofFn (fixedLeafSlot supply p))
    (fixedNodeCounters (fixedLeafPrinterRegisters supply)
      (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨fixedLeafSlot supply p i, 0⟩)
        (.inl 12) 0 ⟨.inl 13, 0⟩)
      (stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply) inputStride
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs)) (.inl 9) = _
  have hn : (.inl 9 : FixedLeafRegister supply) ∉ List.ofFn (fixedLeafSlot supply p) := by
    simp [List.mem_ofFn, fixedLeafSlot]
  rw [cleanupCounters_apply, if_neg hn]
  have hc := fixedNodeCounters_count (fixedLeafPrinterRegisters supply)
    (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨fixedLeafSlot supply p i, 0⟩)
      (.inl 12) 0 ⟨.inl 13, 0⟩)
    (by simp [fixedLeafPrinterRegisters]) (by simp [fixedLeafPrinterRegisters])
    (by simp [fixedLeafPrinterRegisters])
    (stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply) inputStride
      (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs)
  simp only [fixedLeafPrinterRegisters] at hc
  rw [stridedFixedLeafBinding_preserves_control, leafPaddedFormulaClean_layers] at hc
  simpa only [fixedLeafPrinterRegisters, Nat.add_assoc] using hc

theorem stridedSharedFixedGuardedEmitter_count (supply tree : TickGuardFormula tm) (inputStride : Nat) (backward : Bool)
    (cs : FixedLeafRegister supply → Nat) :
    let p := tree.eval (TickIndexGuard.eval (cs (.inl 1)) (cs (.inl 2)))
    (stridedSharedFixedGuardedEmitter supply tree inputStride backward).counters cs (.inl 9) =
      cs (.inl 9) + formulaElementaryLayers p + 1 := by
  unfold stridedSharedFixedGuardedEmitter stridedGuardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  exact stridedFixedLeafEmitter_count supply inputStride _ backward cs

theorem stridedFixedLeafEmitter_private_zero (supply : TickGuardFormula tm) (inputStride : Nat) (p : Formula (TickSymbolicCoordinate tm))
    (backward : Bool) (cs : FixedLeafRegister supply → Nat)
    (j : Fin (leafInputBudget supply.leaves + 1)) (hj : cs (.inr j) = 0) :
    (stridedLeafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) inputStride p (fixedLeafSlot supply p)
      backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)).counters cs (.inr j) = 0 := by
  change cleanupCounters (List.ofFn (fixedLeafSlot supply p))
    (fixedNodeCounters (fixedLeafPrinterRegisters supply)
      (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨fixedLeafSlot supply p i, 0⟩)
        (.inl 12) 0 ⟨.inl 13, 0⟩)
      (stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply) inputStride
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs)) (.inr j) = _
  rw [cleanupCounters_apply]
  split
  · rfl
  · rename_i hn
    rw [fixedNodeCounters_other]
    · rw [stridedCoordinateBindingSequence_preserves_other]
      · exact hj
      · simp only [leafInputBindingTasks, List.forall_mem_ofFn_iff]
        intro i he
        apply hn
        exact List.mem_ofFn.mpr ⟨i, he.symm⟩
    all_goals simp [fixedLeafPrinterRegisters]

theorem stridedSharedFixedGuardedEmitter_private_zero (supply tree : TickGuardFormula tm) (inputStride : Nat) (backward : Bool)
    (cs : FixedLeafRegister supply → Nat) (hj : ∀ j, cs (.inr j) = 0) :
    ∀ j, (stridedSharedFixedGuardedEmitter supply tree inputStride backward).counters cs (.inr j) = 0 := by
  intro j
  unfold stridedSharedFixedGuardedEmitter stridedGuardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  exact stridedFixedLeafEmitter_private_zero supply inputStride _ backward cs j (hj j)

end ShiReversibleGenerator
