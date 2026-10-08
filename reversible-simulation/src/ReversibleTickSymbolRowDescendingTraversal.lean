import ReversibleTickSymbolRowFrames
import ReversibleStridedTickDescendingTraversal
import ReversibleProgramTemplateReentry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickSymbolRowDescendingCode (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) :=
  programReentryCode (tickSymbolRowTemplate tm stack inputStride bound backward) (.inl 2)

/-- The actual fixed finite loop emits every position, decrementing before its coordinate body. -/
theorem tickSymbolRowDescendingTraversal_run (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (capacity count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickSymbolRowTemplate tm stack inputStride bound backward).Labels (Fin 3)))
    (hs : tickDescendingInvariant tm capacity count s) :
    let p := tickSymbolRowTemplate tm stack inputStride bound backward
    CounterRun (tickSymbolRowDescendingCode tm stack inputStride bound backward)
      (withCounter s (.inl 2) count (p.exit 0))
      (descendingSteps (programDescendingBody p (.inl 2)) (programDescendingCost p (.inl 2)) count s)
      (withCounter (descendingResult (programDescendingBody p (.inl 2)) count s) (.inl 2) 0 (p.exit 2)) := by
  let p := tickSymbolRowTemplate tm stack inputStride bound backward
  apply programDescendingTraversal_run p (.inl 2)
    (tickSymbolRowTemplate_embeds tm stack inputStride bound backward)
    (tickSymbolRowTemplate_run tm stack inputStride bound backward)
    (fun k t => tickDescendingInvariant tm capacity k t)
  · intro k t ht
    apply tickSymbolRowTemplate_ready
    simpa [fixedGuardedEmitterReady] using ht.1
  · intro k t ht
    rw [tickSymbolRowTemplate_control_frame tm stack inputStride bound backward _ 2 (by decide)]
    simp
  · intro k t ht
    have hz : fixedGuardedEmitterReady (tickTraversalSupply tm)
        (Function.update t.counters (.inl 2) k) := by
      simpa [fixedGuardedEmitterReady] using ht.1
    refine ⟨tickSymbolRowTemplate_ready_preserved tm stack inputStride bound backward _ hz, ?_, ?_⟩
    · change p.counters (Function.update t.counters (.inl 2) k) (.inl 1) = capacity
      rw [tickSymbolRowTemplate_control_frame tm stack inputStride bound backward _ 1 (by decide)]
      simpa using ht.2.1
    · exact Nat.le_trans (Nat.le_succ k) ht.2.2
  · exact hs

end ShiReversibleGenerator
