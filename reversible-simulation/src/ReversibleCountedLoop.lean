import ReversibleCounterMacros

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Iterate a proved fixed body at the descending counter values. -/
def descendingResult (body : Nat → CounterCfg R L → CounterCfg R L) :
    Nat → CounterCfg R L → CounterCfg R L
  | 0, s => s
  | k + 1, s => descendingResult body k (body k s)

/-- Count both loop-control instructions and each body's actual run; the last test costs one. -/
def descendingSteps (body : Nat → CounterCfg R L → CounterCfg R L)
    (cost : Nat → CounterCfg R L → Nat) : Nat → CounterCfg R L → Nat
  | 0, _ => 1
  | k + 1, s => 2 + cost k s + descendingSteps body cost k (body k s)

/-- A bounded traversal uses one fixed control graph. The semantic body may depend on
runtime values only through its separately proved actual counted instruction run. -/
theorem descending_counter_run (code : L → CounterInstr R L) (r : R)
    (loop pop entry stop : L)
    (hloop : code loop = .branch r stop pop) (hpop : code pop = .dec r entry)
    (body : Nat → CounterCfg R L → CounterCfg R L) (cost : Nat → CounterCfg R L → Nat)
    (invariant : Nat → CounterCfg R L → Prop)
    (hbody : ∀ k s, invariant (k + 1) s →
      CounterRun code (withCounter s r k entry) (cost k s) (withCounter (body k s) r k loop))
    (hnext : ∀ k s, invariant (k + 1) s → invariant k (body k s))
    (k : Nat) (s : CounterCfg R L) (hs : invariant k s) :
    CounterRun code (withCounter s r k loop) (descendingSteps body cost k s)
      (withCounter (descendingResult body k s) r 0 stop) := by
  induction k generalizing s with
  | zero =>
      apply CounterRun.next (l := loop) rfl
      simpa [hloop, CounterInstr.eval, withCounter, descendingResult, descendingSteps] using
        CounterRun.refl (withCounter s r 0 stop)
  | succ k ih =>
      have hb := CounterRun.trans code (hbody k s hs) (ih (body k s) (hnext k s hs))
      have hp := CounterRun.next (code := code) (l := pop)
        (s := withCounter s r (k + 1) pop) rfl
        (by simpa [hpop, withCounter, CounterInstr.eval] using hb)
      have hl := CounterRun.next (code := code) (l := loop)
        (s := withCounter s r (k + 1) loop) rfl
        (by simpa [hloop, withCounter, CounterInstr.eval] using hp)
      convert hl using 1 <;> simp [descendingSteps, descendingResult, withCounter] <;> omega

/-- A uniform per-body bound bounds the traversal, including its final zero test. -/
theorem descendingSteps_bound (body : Nat → CounterCfg R L → CounterCfg R L)
    (cost : Nat → CounterCfg R L → Nat) (bound : Nat)
    (invariant : Nat → CounterCfg R L → Prop)
    (h : ∀ k s, invariant (k + 1) s → cost k s ≤ bound)
    (hnext : ∀ k s, invariant (k + 1) s → invariant k (body k s))
    (k : Nat) (s : CounterCfg R L) (hs : invariant k s) :
    descendingSteps body cost k s ≤ k * (bound + 2) + 1 := by
  induction k generalizing s with
  | zero => simp [descendingSteps]
  | succ k ih =>
      have hb := h k s hs
      have hi := ih (body k s) (hnext k s hs)
      simp only [descendingSteps, Nat.succ_mul]
      omega

end ShiReversibleGenerator
