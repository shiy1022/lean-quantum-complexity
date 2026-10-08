import ReversibleTickSelectedLeafBounds
import ReversibleSymbolicWireBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

/-- Actual private binding and printing reset all three address fields to the wire budget. -/
theorem stridedFixedLeafEmitter_fields_bound (supply : TickGuardFormula tm)
    (inputStride : Nat) (p : Formula (TickSymbolicCoordinate tm)) (hp : p ∈ supply.leaves)
    (backward : Bool) (cs : FixedLeafRegister supply → Nat) (bound : Nat)
    (hi : ∀ i : Fin p.inputList.length, stridedTickCoordinateAddress tm (fixedLeafBindingRegisters supply)
      inputStride p.inputList[i.val] cs ≤ bound)
    (hb : cs (.inl 12) + p.size ≤ bound) (hz : cs (.inl 13) ≤ bound) :
    let final := (stridedLeafPaddedCounterTemplate tm (fixedLeafBindingRegisters supply) inputStride p
      (fixedLeafSlot supply p) backward (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)).counters cs
    final (.inl 6) ≤ bound ∧ final (.inl 7) ≤ bound ∧ final (.inl 8) ≤ bound := by
  let inputs := fun i : Fin p.inputList.length => (⟨fixedLeafSlot supply p i, 0⟩ : SymbolicWire (FixedLeafRegister supply))
  let after := stridedCoordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply) inputStride
    (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs
  let ts := paddedFormulaPrinterTemplates backward p.intern inputs (.inl 12) 0 ⟨.inl 13, 0⟩
  have hs := paddedFormulaPrinter_stable backward p.intern inputs (.inl 12) 0 ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply)
    (by simp [fixedLeafPrinterRegisters, NodePrinterRegisters.SourceStable])
    (fun i => fixedLeafSlot_source_stable supply p i)
    (by simp [fixedLeafPrinterRegisters, NodePrinterRegisters.SourceStable])
  have hw := paddedFormulaPrinter_wires_bound backward p.intern inputs (.inl 12) 0 ⟨.inl 13, 0⟩ after bound
    (by
      intro i
      simp only [inputs, SymbolicWire.eval, Nat.add_zero]
      dsimp only [after]
      rw [stridedLeafInputBindingTasks_slot_values tm (fixedLeafBindingRegisters supply) inputStride p
        (fixedLeafSlot supply p) (fun i => fixedLeafSlot_valid supply p i) (fixedLeafSlot_injective supply p hp)]
      simpa only [stridedTickCoordinateAddress, CoordinateBindingRegisters.withTarget] using hi i)
    (by
      dsimp only [after]
      rw [stridedFixedLeafBinding_preserves_control]
      simpa only [Formula.intern_size, Nat.add_zero] using hb)
    (by
      simp only [SymbolicWire.eval, Nat.add_zero]
      dsimp only [after]
      rw [stridedFixedLeafBinding_preserves_control]
      exact hz)
  have hf := fixedNodeCounters_fields_bound (fixedLeafPrinterRegisters supply) ts
    (by simp [fixedLeafPrinterRegisters]) (by simp [fixedLeafPrinterRegisters]) (by simp [fixedLeafPrinterRegisters])
    (by simp [fixedLeafPrinterRegisters]) (by simp [fixedLeafPrinterRegisters]) (by simp [fixedLeafPrinterRegisters])
    hs (paddedFormulaPrinter_nonempty backward p.intern inputs (.inl 12) 0 ⟨.inl 13, 0⟩) after bound hw
  have hn : ∀ q : Fin 14, (.inl q : FixedLeafRegister supply) ∉ List.ofFn (fixedLeafSlot supply p) := by
    intro q
    simp [List.mem_ofFn, fixedLeafSlot]
  change cleanupCounters (List.ofFn (fixedLeafSlot supply p)) (fixedNodeCounters (fixedLeafPrinterRegisters supply) ts after)
    (.inl 6) ≤ bound ∧ cleanupCounters (List.ofFn (fixedLeafSlot supply p))
    (fixedNodeCounters (fixedLeafPrinterRegisters supply) ts after) (.inl 7) ≤ bound ∧
    cleanupCounters (List.ofFn (fixedLeafSlot supply p))
    (fixedNodeCounters (fixedLeafPrinterRegisters supply) ts after) (.inl 8) ≤ bound
  simpa only [cleanupCounters_apply, if_neg (hn 6), if_neg (hn 7), if_neg (hn 8), fixedLeafPrinterRegisters] using hf

end ShiReversibleGenerator
