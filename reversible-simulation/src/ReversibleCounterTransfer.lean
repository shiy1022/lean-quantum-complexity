import ReversibleCounterMacros

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def transferState (base : CounterCfg R L) (r q : R) (n m : Nat) (pc : L) : CounterCfg R L :=
  ⟨some pc, Function.update (Function.update base.counters r n) q m, base.output⟩

@[simp] theorem transferState_left (base : CounterCfg R L) (r q : R) (hq : r ≠ q)
    (n m : Nat) (pc : L) : (transferState base r q n m pc).counters r = n := by
  simp [transferState, Function.update_of_ne hq]

@[simp] theorem transferState_right (base : CounterCfg R L) (r q : R)
    (n m : Nat) (pc : L) : (transferState base r q n m pc).counters q = m := by
  simp [transferState]

@[simp] theorem transferState_dec (base : CounterCfg R L) (r q : R) (hq : r ≠ q)
    (n m : Nat) (pc next : L) :
    (CounterInstr.dec r next).eval (transferState base r q n m pc) =
      transferState base r q (n - 1) m next := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hj : j = r
    · subst j; simp [CounterInstr.eval, transferState, hq]
    · by_cases hjq : j = q
      · subst j; simp [CounterInstr.eval, transferState, Ne.symm hq]
      · simp [CounterInstr.eval, transferState, hj, hjq]
  · rfl

@[simp] theorem transferState_inc (base : CounterCfg R L) (r q : R)
    (n m : Nat) (pc next : L) :
    (CounterInstr.inc q next).eval (transferState base r q n m pc) =
      transferState base r q n (m + 1) next := by
  simp [CounterInstr.eval, transferState]

/-- Transfer one unary counter into another in exactly `3*n+1` instructions. -/
theorem transfer_counter_run (code : L → CounterInstr R L) (r q : R) (hq : r ≠ q)
    (loop pop inc stop : L) (hloop : code loop = .branch r stop pop)
    (hpop : code pop = .dec r inc) (hinc : code inc = .inc q loop)
    (base : CounterCfg R L) (n m : Nat) :
    CounterRun code (transferState base r q n m loop) (3 * n + 1)
      (transferState base r q 0 (m + n) stop) := by
  induction n generalizing m with
  | zero =>
    apply CounterRun.next (code := code) (l := loop) rfl
    simpa [hloop, CounterInstr.eval, transferState, hq] using
      CounterRun.refl (transferState base r q 0 m stop)
  | succ n ih =>
    have h₁ := CounterRun.next (code := code) (l := inc) (s := transferState base r q n m inc) rfl
      (by simpa [hinc] using ih (m + 1))
    have h₂ := CounterRun.next (code := code) (l := pop) (s := transferState base r q (n + 1) m pop) rfl
      (by simpa [hpop, transferState_dec base r q hq] using h₁)
    have h₃ := CounterRun.next (code := code) (l := loop) (s := transferState base r q (n + 1) m loop) rfl
      (by simpa [hloop, CounterInstr.eval, transferState, hq] using h₂)
    convert h₃ using 1 <;> simp [transferState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

end ShiReversibleGenerator
