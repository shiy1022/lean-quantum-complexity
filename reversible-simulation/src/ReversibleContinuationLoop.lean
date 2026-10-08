import ReversibleTickTraversalFinalBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Two private loop-control labels, with an external continuation summand. -/
abbrev LoopContinuation (L : Type) := Unit ⊕ (Unit ⊕ L)

def loopContinuationCaller (caller : L → CounterInstr R L) :
    LoopContinuation L → CounterInstr R (LoopContinuation L)
  | .inl _ => .halt
  | .inr (.inl _) => .halt
  | .inr (.inr l) => (caller l).relabel (fun j => .inr (.inr j))

/-- A genuine finite loop graph that can return to an arbitrary caller. -/
noncomputable def continuationLoopCode (p : CounterProgramTemplate R) (remaining : R)
    (caller : L → CounterInstr R L) (stop : L) :
    p.Labels (LoopContinuation L) → CounterInstr R (p.Labels (LoopContinuation L)) := by
  classical
  exact reentryCode (p.code (loopContinuationCaller caller) (.inl ())) remaining
    (p.exit (.inl ())) (p.exit (.inr (.inl ()))) (p.entry (.inl ())) (p.exit (.inr (.inr stop)))

theorem continuationLoopCode_test (p : CounterProgramTemplate R) (remaining : R)
    (caller : L → CounterInstr R L) (stop : L) :
    continuationLoopCode p remaining caller stop (p.exit (.inl ())) =
      .branch remaining (p.exit (.inr (.inr stop))) (p.exit (.inr (.inl ()))) := by
  classical
  exact reentryCode_loop _ _ _ _ _ _

theorem continuationLoopCode_pop (p : CounterProgramTemplate R) (remaining : R)
    (he : p.Embeds) (caller : L → CounterInstr R L) (stop : L) :
    continuationLoopCode p remaining caller stop (p.exit (.inr (.inl ()))) =
      .dec remaining (p.entry (.inl ())) := by
  classical
  apply reentryCode_pop
  intro h
  have hh := p.exit_injective he (LoopContinuation L) h
  cases hh

theorem continuationLoopCode_embed (p : CounterProgramTemplate R) (remaining : R)
    (he : p.Embeds) (caller : L → CounterInstr R L) (stop l : L) :
    continuationLoopCode p remaining caller stop (p.exit (.inr (.inr l))) =
      (caller l).relabel (fun j => p.exit (.inr (.inr j))) := by
  classical
  have hn : p.exit (L := LoopContinuation L) (.inr (.inr l)) ≠ p.exit (.inl ()) := by
    intro h; have hh := p.exit_injective he (LoopContinuation L) h; cases hh
  have hp : p.exit (L := LoopContinuation L) (.inr (.inr l)) ≠ p.exit (.inr (.inl ())) := by
    intro h; have hh := p.exit_injective he (LoopContinuation L) h; cases hh
  unfold continuationLoopCode reentryCode
  rw [if_neg hn,if_neg hp,he]
  simp only [loopContinuationCaller]
  cases caller l <;> rfl

/-- Replacing only the private halt labels preserves the actual counted body execution. -/
theorem continuationLoopCode_body (p : CounterProgramTemplate R) (remaining : R)
    (he : p.Embeds) (hr : p.Runs) (caller : L → CounterInstr R L) (stop : L)
    (cs : R → Nat) (ys : List Bool) (hready : p.ready cs) :
    CounterRun (continuationLoopCode p remaining caller stop)
      ⟨some (p.entry (.inl ())), cs, ys⟩ (p.steps cs)
      ⟨some (p.exit (.inl ())), p.counters cs, p.bytes cs ++ ys⟩ := by
  classical
  apply reentryCode_preserves_run (p.code (loopContinuationCaller caller) (.inl ())) remaining
    (p.exit (.inl ())) (p.exit (.inr (.inl ()))) (p.entry (.inl ())) (p.exit (.inr (.inr stop)))
  · simpa only [loopContinuationCaller,CounterInstr.relabel] using he (LoopContinuation L) (loopContinuationCaller caller) (.inl ()) (.inl ())
  · simpa only [loopContinuationCaller,CounterInstr.relabel] using he (LoopContinuation L) (loopContinuationCaller caller) (.inl ()) (.inr (.inl ()))
  · exact hr (LoopContinuation L) (loopContinuationCaller caller) (.inl ()) cs ys hready
  · simp

end ShiReversibleGenerator
