import ReversibleCounterProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def withCounter (s : CounterCfg R L) (r : R) (n : Nat) (pc : L) : CounterCfg R L :=
  ⟨some pc, Function.update s.counters r n, s.output⟩

@[simp] theorem withCounter_inc (s : CounterCfg R L) (r : R) (n : Nat) (pc next : L) :
    (CounterInstr.inc r next).eval (withCounter s r n pc) = withCounter s r (n + 1) next := by
  simp [CounterInstr.eval, withCounter]

@[simp] theorem withCounter_dec (s : CounterCfg R L) (r : R) (n : Nat) (pc next : L) :
    (CounterInstr.dec r next).eval (withCounter s r n pc) = withCounter s r (n - 1) next := by
  simp [CounterInstr.eval, withCounter]

/-- A reusable clearing loop, with an exact instruction count and unchanged other registers/output. -/
theorem clear_counter_run (code : L → CounterInstr R L) (r : R) (loop pop stop : L)
    (hloop : code loop = .branch r stop pop) (hpop : code pop = .dec r loop)
    (s : CounterCfg R L) (n : Nat) :
    CounterRun code (withCounter s r n loop) (2 * n + 1) (withCounter s r 0 stop) := by
  induction n with
  | zero =>
    apply CounterRun.next (code := code) (l := loop) rfl
    simpa [hloop, CounterInstr.eval, withCounter] using CounterRun.refl (withCounter s r 0 stop)
  | succ n ih =>
    have hp := CounterRun.next (code := code) (l := pop) (s := withCounter s r (n + 1) pop) rfl
      (by simpa [hpop] using ih)
    have hl := CounterRun.next (code := code) (l := loop) (s := withCounter s r (n + 1) loop) rfl
      (by simpa [hloop, CounterInstr.eval, withCounter] using hp)
    simpa [withCounter, Nat.mul_add, Nat.add_assoc] using hl

def printState (s : CounterCfg R L) (r : R) (n : Nat) (ys : List Bool) (pc : L) : CounterCfg R L :=
  ⟨some pc, Function.update s.counters r n, ys⟩

/-- Emit a unary block by consuming its counter, preserving every other counter. -/
theorem emit_counter_run (code : L → CounterInstr R L) (r : R) (loop pop emit stop : L) (b : Bool)
    (hloop : code loop = .branch r stop pop) (hpop : code pop = .dec r emit)
    (hemit : code emit = .emit b loop) (s : CounterCfg R L) (n : Nat) (ys : List Bool) :
    CounterRun code (printState s r n ys loop) (3 * n + 1)
      (printState s r 0 (List.replicate n b ++ ys) stop) := by
  induction n generalizing ys with
  | zero =>
    apply CounterRun.next (code := code) (l := loop) rfl
    simpa [hloop, CounterInstr.eval, printState] using CounterRun.refl (printState s r 0 ys stop)
  | succ n ih =>
    have h₁ := CounterRun.next (code := code) (l := emit) (s := printState s r n ys emit) rfl
      (by simpa [hemit, CounterInstr.eval, printState] using ih (b :: ys))
    have h₂ := CounterRun.next (code := code) (l := pop) (s := printState s r (n + 1) ys pop) rfl
      (by simpa [hpop, CounterInstr.eval, printState] using h₁)
    have h₃ := CounterRun.next (code := code) (l := loop) (s := printState s r (n + 1) ys loop) rfl
      (by simpa [hloop, CounterInstr.eval, printState] using h₂)
    simpa [printState, List.replicate_succ', List.append_assoc, Nat.mul_add, Nat.add_assoc] using h₃

end ShiReversibleGenerator
