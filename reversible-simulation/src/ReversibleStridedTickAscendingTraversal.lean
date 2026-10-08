import ReversibleStridedTickAscendingBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def stridedTickAscendingCode (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) :=
  programReentryCode (stridedTickAscendingBody tm kind inputStride bound backward) (tickTraversalSpare tm 0)

def tickAscendingInvariant (tm : Turing.FinTM2) (capacity k : Nat)
    {L : Type} (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) L) : Prop :=
  fixedGuardedEmitterReady (tickTraversalSupply tm) s.counters ∧ s.counters (.inl 1) = capacity ∧
    s.counters (.inl 2) + k = capacity

/-- A separate remaining counter drives actual increasing coordinate emission without changing the input window. -/
theorem stridedTickAscendingTraversal_run (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (capacity count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((stridedTickAscendingBody tm kind inputStride bound backward).Labels (Fin 3)))
    (hs : tickAscendingInvariant tm capacity count s) :
    let p := stridedTickAscendingBody tm kind inputStride bound backward
    let remaining := tickTraversalSpare tm 0
    CounterRun (stridedTickAscendingCode tm kind inputStride bound backward)
      (withCounter s remaining count (p.exit 0))
      (descendingSteps (programDescendingBody p remaining) (programDescendingCost p remaining) count s)
      (withCounter (descendingResult (programDescendingBody p remaining) count s) remaining 0 (p.exit 2)) := by
  let p := stridedTickAscendingBody tm kind inputStride bound backward
  let remaining := tickTraversalSpare tm 0
  apply programDescendingTraversal_run p remaining
    (stridedTickAscendingBody_embeds tm kind inputStride bound backward)
    (stridedTickAscendingBody_run tm kind inputStride bound backward)
    (fun k t => tickAscendingInvariant tm capacity k t)
  · intro k t ht
    apply stridedTickAscendingBody_ready
    simpa [remaining, tickTraversalSpare, fixedGuardedEmitterReady] using ht.1
  · intro k t ht
    rw [stridedTickAscendingBody_spare_frame tm kind inputStride bound backward _ 0]
    simp [remaining]
  · intro k t ht
    have hz : fixedGuardedEmitterReady (tickTraversalSupply tm)
        (Function.update t.counters remaining k) := by
      simpa [remaining, tickTraversalSpare, fixedGuardedEmitterReady] using ht.1
    refine ⟨stridedTickAscendingBody_ready_preserved tm kind inputStride bound backward _ hz, ?_, ?_⟩
    · change p.counters (Function.update t.counters remaining k) (.inl 1) = capacity
      rw [stridedTickAscendingBody_capacity]
      simpa [remaining, tickTraversalSpare] using ht.2.1
    · change p.counters (Function.update t.counters remaining k) (.inl 2) + k = capacity
      rw [stridedTickAscendingBody_position]
      simpa [remaining, tickTraversalSpare, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.2.2
  · exact hs

end ShiReversibleGenerator
