import ReversibleStridedTickCoordinateFrames
import ReversibleProgramTemplateReentry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def stridedTickDescendingCode (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) :=
  programReentryCode (stridedTickCoordinateBody tm kind inputStride bound backward) (.inl 2)

def tickDescendingInvariant (tm : Turing.FinTM2) (capacity k : Nat)
    {L : Type} (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) L) : Prop :=
  fixedGuardedEmitterReady (tickTraversalSupply tm) s.counters ∧ s.counters (.inl 1) = capacity ∧ k ≤ capacity

/-- The actual fixed finite loop emits every position, decrementing before its coordinate body. -/
theorem stridedTickDescendingTraversal_run (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (capacity count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((stridedTickCoordinateBody tm kind inputStride bound backward).Labels (Fin 3)))
    (hs : tickDescendingInvariant tm capacity count s) :
    let p := stridedTickCoordinateBody tm kind inputStride bound backward
    CounterRun (stridedTickDescendingCode tm kind inputStride bound backward)
      (withCounter s (.inl 2) count (p.exit 0))
      (descendingSteps (programDescendingBody p (.inl 2)) (programDescendingCost p (.inl 2)) count s)
      (withCounter (descendingResult (programDescendingBody p (.inl 2)) count s) (.inl 2) 0 (p.exit 2)) := by
  let p := stridedTickCoordinateBody tm kind inputStride bound backward
  apply programDescendingTraversal_run p (.inl 2)
    (stridedTickCoordinateBody_embeds tm kind inputStride bound backward)
    (stridedTickCoordinateBody_run tm kind inputStride bound backward)
    (fun k t => tickDescendingInvariant tm capacity k t)
  · intro k t ht
    apply stridedTickCoordinateBody_ready
    simpa [fixedGuardedEmitterReady] using ht.1
  · intro k t ht
    rw [stridedTickCoordinateBody_control_frame tm kind inputStride bound backward _ 2 (by decide)]
    simp
  · intro k t ht
    have hz : fixedGuardedEmitterReady (tickTraversalSupply tm)
        (Function.update t.counters (.inl 2) k) := by
      simpa [fixedGuardedEmitterReady] using ht.1
    refine ⟨stridedTickCoordinateBody_ready_preserved tm kind inputStride bound backward _ hz, ?_, ?_⟩
    · change p.counters (Function.update t.counters (.inl 2) k) (.inl 1) = capacity
      rw [stridedTickCoordinateBody_control_frame tm kind inputStride bound backward _ 1 (by decide)]
      simpa using ht.2.1
    · exact Nat.le_trans (Nat.le_succ k) ht.2.2
  · exact hs

end ShiReversibleGenerator
