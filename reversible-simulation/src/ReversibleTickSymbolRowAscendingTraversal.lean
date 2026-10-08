import ReversibleTickSymbolRowAscendingBody
import ReversibleStridedTickAscendingTraversal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickSymbolRowAscendingCode (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) :=
  programReentryCode (tickSymbolRowAscendingBody tm stack inputStride bound backward) (tickTraversalSpare tm 0)

/-- A separate remaining counter drives actual increasing coordinate emission without changing the input window. -/
theorem tickSymbolRowAscendingTraversal_run (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (capacity count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickSymbolRowAscendingBody tm stack inputStride bound backward).Labels (Fin 3)))
    (hs : tickAscendingInvariant tm capacity count s) :
    let p := tickSymbolRowAscendingBody tm stack inputStride bound backward
    let remaining := tickTraversalSpare tm 0
    CounterRun (tickSymbolRowAscendingCode tm stack inputStride bound backward)
      (withCounter s remaining count (p.exit 0))
      (descendingSteps (programDescendingBody p remaining) (programDescendingCost p remaining) count s)
      (withCounter (descendingResult (programDescendingBody p remaining) count s) remaining 0 (p.exit 2)) := by
  let p := tickSymbolRowAscendingBody tm stack inputStride bound backward
  let remaining := tickTraversalSpare tm 0
  apply programDescendingTraversal_run p remaining
    (tickSymbolRowAscendingBody_embeds tm stack inputStride bound backward)
    (tickSymbolRowAscendingBody_run tm stack inputStride bound backward)
    (fun k t => tickAscendingInvariant tm capacity k t)
  · intro k t ht
    apply tickSymbolRowAscendingBody_ready
    simpa [remaining, tickTraversalSpare, fixedGuardedEmitterReady] using ht.1
  · intro k t ht
    rw [tickSymbolRowAscendingBody_spare_frame tm stack inputStride bound backward _ 0]
    simp [remaining]
  · intro k t ht
    have hz : fixedGuardedEmitterReady (tickTraversalSupply tm)
        (Function.update t.counters remaining k) := by
      simpa [remaining, tickTraversalSpare, fixedGuardedEmitterReady] using ht.1
    refine ⟨tickSymbolRowAscendingBody_ready_preserved tm stack inputStride bound backward _ hz, ?_, ?_⟩
    · change p.counters (Function.update t.counters remaining k) (.inl 1) = capacity
      rw [tickSymbolRowAscendingBody_capacity]
      simpa [remaining, tickTraversalSpare] using ht.2.1
    · change p.counters (Function.update t.counters remaining k) (.inl 2) + k = capacity
      rw [tickSymbolRowAscendingBody_position]
      simpa [remaining, tickTraversalSpare, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.2.2
  · exact hs

end ShiReversibleGenerator
