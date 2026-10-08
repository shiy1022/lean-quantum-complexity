import ReversibleSharedEmitterCleanupCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {tm : Turing.FinTM2}

theorem sharedFixedGuardedEmitter_payload (supply tree : TickGuardFormula tm)
    (hsub : ∀ p ∈ tree.leaves, p ∈ supply.leaves) (backward : Bool)
    (cs : FixedLeafRegister supply → Nat) (bound : Nat) (hz : cs (.inl 13) = cs (.inl 12) + bound) :
    let p := tree.eval (TickIndexGuard.eval (cs (.inl 1)) (cs (.inl 2)))
    let nodes := p.paddedCompile (fun c => cs (.inl 0) + naturalConfigurationAddress tm (cs (.inl 1))
      (tickSymbolicCoordinateEval (cs (.inl 1)) (cs (.inl 2)) c)) (cs (.inl 12)) bound
    (sharedFixedGuardedEmitter supply tree backward).bytes cs =
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  let p := tree.eval (TickIndexGuard.eval (cs (.inl 1)) (cs (.inl 2)))
  have hz' :
      let after := coordinateBindingSequenceCounters tm (fixedLeafBindingRegisters supply)
        (leafInputBindingTasks tm p (fixedLeafSlot supply p)) cs
      (SymbolicWire.mk (.inl 13 : FixedLeafRegister supply) 0).eval after = after (.inl 12) + 0 + bound := by
    dsimp only [SymbolicWire.eval]
    rw [fixedLeafBinding_preserves_control, fixedLeafBinding_preserves_control]
    simpa only [Nat.add_zero] using hz
  have h := guardedLeafCounterTemplate_bytes tm (fixedLeafBindingRegisters supply) (fixedLeafGuardRegisters supply)
    (fixedLeafSlot supply) backward (.inl 12) 0 bound ⟨.inl 13, 0⟩ (fixedLeafPrinterRegisters supply) tree cs
    (fun p hp i => fixedLeafSlot_valid supply p i)
    (fun p hp => fixedLeafSlot_injective supply p (hsub p hp))
    (by simp [fixedLeafPrinterRegisters]) (by simp [fixedLeafPrinterRegisters]) (by simp [fixedLeafPrinterRegisters])
    (by simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters])
    (by simp [NodePrinterRegisters.SourceStable, fixedLeafPrinterRegisters])
    (fun p hp i => fixedLeafSlot_source_stable supply p i) hz'
  dsimp only at h
  rw [fixedLeafBinding_preserves_control] at h
  simpa only [sharedFixedGuardedEmitter, tickCoordinateAddress, fixedLeafBindingRegisters,
    fixedLeafGuardRegisters, Nat.add_zero] using h

/-- Every header/memory/cell kind uses one common finite register supply and prints the actual tick formula. -/
theorem machineTickEmitter_payload (tm : Turing.FinTM2) (kind : TickTreeKind tm) (backward : Bool)
    (cs : FixedLeafRegister (machineTickSupply tm) → Nat) (bound : Nat)
    (hz : cs (.inl 13) = cs (.inl 12) + bound) (hi : cs (.inl 2) < cs (.inl 1)) :
    let i : Fin (cs (.inl 1)) := ⟨cs (.inl 2), hi⟩
    let nodes := (boundedTickFormulaForKind tm (cs (.inl 1)) i kind).paddedCompile
      (fun j => cs (.inl 0) + j.val) (cs (.inl 12)) bound
    (sharedFixedGuardedEmitter (machineTickSupply tm) (tickTreeForKind tm kind) backward).bytes cs =
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  have h := sharedFixedGuardedEmitter_payload (machineTickSupply tm) (tickTreeForKind tm kind)
    (machineTickSupply_contains tm kind) backward cs bound hz
  dsimp only at h ⊢
  rw [tickTreeForKind_paddedCompile_relocated tm (cs (.inl 1)) (cs (.inl 0)) (cs (.inl 12)) bound
    ⟨cs (.inl 2), hi⟩ kind] at h
  exact h

end ShiReversibleGenerator
