import ReversibleContinuationLoop
import ReversibleDescendingTemplateData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Actual counted traversal returns to the caller's external continuation. -/
theorem continuationDescendingTraversal_run (p : CounterProgramTemplate R) (remaining : R)
    (he : p.Embeds) (hr : p.Runs) (caller : L → CounterInstr R L) (stop : L)
    (invariant : Nat → CounterCfg R (p.Labels (LoopContinuation L)) → Prop)
    (hready : ∀ k s, invariant (k+1) s → p.ready (Function.update s.counters remaining k))
    (hframe : ∀ k s, invariant (k+1) s → p.counters (Function.update s.counters remaining k) remaining = k)
    (hnext : ∀ k s, invariant (k+1) s → invariant k (templateDescendingBody p remaining k s))
    (k : Nat) (s : CounterCfg R (p.Labels (LoopContinuation L))) (hs : invariant k s) :
    CounterRun (continuationLoopCode p remaining caller stop)
      (withCounter s remaining k (p.exit (.inl ())))
      (descendingSteps (templateDescendingBody p remaining) (templateDescendingCost p remaining) k s)
      (withCounter (descendingResult (templateDescendingBody p remaining) k s) remaining 0
        (p.exit (.inr (.inr stop)))) := by
  apply descending_counter_run _ _ _ _ _ _ (continuationLoopCode_test p remaining caller stop)
    (continuationLoopCode_pop p remaining he caller stop) _ _ invariant _ hnext k s hs
  intro j t ht
  have h := continuationLoopCode_body p remaining he hr caller stop
    (Function.update t.counters remaining j) t.output (hready j t ht)
  have hf : Function.update (p.counters (Function.update t.counters remaining j)) remaining j =
      p.counters (Function.update t.counters remaining j) := by
    funext q
    by_cases hq : q = remaining
    · subst q; simpa only [Function.update_self] using (hframe j t ht).symm
    · simp [hq]
  simpa only [withCounter,templateDescendingBody,templateDescendingCost,hf] using h

end ShiReversibleGenerator
