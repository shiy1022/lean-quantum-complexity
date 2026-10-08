import ReversibleCounterCopy

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Four distinct unary registers: consumed multiplier, preserved multiplicand,
accumulator and zero restoration scratch. -/
def multiplyState (base : CounterCfg R L) (r q dst tmp : R)
    (k n m : Nat) (pc : L) : CounterCfg R L :=
  copyState (withCounter base r k pc) q dst tmp n m 0 pc

@[simp] theorem multiplyState_outer (base : CounterCfg R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp)
    (k n m : Nat) (pc : L) :
    (multiplyState base r q dst tmp k n m pc).counters r = k := by
  simp [multiplyState, copyState, withCounter, hrq, hrd, hrt]

@[simp] theorem multiplyState_dec (base : CounterCfg R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp)
    (k n m : Nat) (pc next : L) :
    (CounterInstr.dec r next).eval (multiplyState base r q dst tmp k n m pc) =
      multiplyState base r q dst tmp (k - 1) n m next := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hj : j = r
    · subst j; simp [CounterInstr.eval, multiplyState, copyState, withCounter, hrq, hrd, hrt]
    · by_cases ht : j = tmp
      · subst j; simp [CounterInstr.eval, multiplyState, copyState, withCounter, Ne.symm hrt]
      · by_cases hd : j = dst
        · subst j; simp [CounterInstr.eval, multiplyState, copyState, withCounter, Ne.symm hrd, ht]
        · by_cases hq : j = q
          · subst j; simp [CounterInstr.eval, multiplyState, copyState, withCounter, Ne.symm hrq, ht, hd]
          · simp [CounterInstr.eval, multiplyState, copyState, withCounter, hj, ht, hd, hq]
  · rfl

/-- Repeated nonconsuming addition is actual counter-program multiplication.
The multiplier is consumed, the multiplicand preserved, and scratch cleared.
The clock includes every branch, decrement and scratch-restoration instruction. -/
theorem multiply_counter_run (code : L → CounterInstr R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp)
    (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (outer consume loop pop add save restore take back stop : L)
    (houter : code outer = .branch r stop consume) (hconsume : code consume = .dec r loop)
    (hloop : code loop = .branch q restore pop) (hpop : code pop = .dec q add)
    (hadd : code add = .inc dst save) (hsave : code save = .inc tmp loop)
    (hrestore : code restore = .branch tmp outer take) (htake : code take = .dec tmp back)
    (hback : code back = .inc q restore)
    (base : CounterCfg R L) (k n m : Nat) :
    CounterRun code (multiplyState base r q dst tmp k n m outer) (k * (7 * n + 4) + 1)
      (multiplyState base r q dst tmp 0 n (m + k * n) stop) := by
  induction k generalizing m with
  | zero =>
    apply CounterRun.next (code := code) (l := outer) rfl
    simpa [houter, CounterInstr.eval, multiplyState, copyState, withCounter, hrq, hrd, hrt] using
      CounterRun.refl (multiplyState base r q dst tmp 0 n m stop)
  | succ k ih =>
    have hc : CounterRun code (multiplyState base r q dst tmp k n m loop) (7 * n + 2)
        (multiplyState base r q dst tmp k n (m + n) outer) :=
      copy_counter_run code q dst tmp hqd hqt hdt loop pop add save restore take back outer
        hloop hpop hadd hsave hrestore htake hback (withCounter base r k loop) n m
    have h := CounterRun.trans (R := R) (L := L) code hc (ih (m + n))
    have hp := CounterRun.next (code := code) (l := consume)
      (s := multiplyState base r q dst tmp (k + 1) n m consume) rfl
      (by simpa [hconsume, multiplyState_dec base r q dst tmp hrq hrd hrt] using h)
    have ho := CounterRun.next (code := code) (l := outer)
      (s := multiplyState base r q dst tmp (k + 1) n m outer) rfl
      (by simpa [houter, CounterInstr.eval, multiplyState, copyState, withCounter, hrq, hrd, hrt] using hp)
    convert ho using 1 <;> simp [multiplyState, copyState, withCounter, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> ring

end ShiReversibleGenerator
