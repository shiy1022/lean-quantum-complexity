import ReversibleCounterTransfer

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def copyState (base : CounterCfg R L) (r q tmp : R) (n m z : Nat) (pc : L) : CounterCfg R L :=
  ⟨some pc, Function.update (Function.update (Function.update base.counters r n) q m) tmp z, base.output⟩

@[simp] theorem copyState_dec (base : CounterCfg R L) (r q tmp : R)
    (hrq : r ≠ q) (hrt : r ≠ tmp) (hqt : q ≠ tmp) (n m z : Nat) (pc next : L) :
    (CounterInstr.dec r next).eval (copyState base r q tmp n m z pc) =
      copyState base r q tmp (n - 1) m z next := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases ht : j = tmp
    · subst j; simp [CounterInstr.eval, copyState, Ne.symm hrt]
    · by_cases hq : j = q
      · subst j; simp [CounterInstr.eval, copyState, Ne.symm hrq, hqt]
      · by_cases hr : j = r
        · subst j; simp [CounterInstr.eval, copyState, hrq, hrt]
        · simp [CounterInstr.eval, copyState, ht, hq, hr]
  · rfl

@[simp] theorem copyState_inc_middle (base : CounterCfg R L) (r q tmp : R)
    (hqt : q ≠ tmp) (n m z : Nat) (pc next : L) :
    (CounterInstr.inc q next).eval (copyState base r q tmp n m z pc) =
      copyState base r q tmp n (m + 1) z next := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases ht : j = tmp
    · subst j; simp [CounterInstr.eval, copyState, Ne.symm hqt]
    · by_cases hq : j = q
      · subst j; simp [CounterInstr.eval, copyState, hqt]
      · simp [CounterInstr.eval, copyState, ht, hq]
  · rfl

@[simp] theorem copyState_inc_last (base : CounterCfg R L) (r q tmp : R)
    (n m z : Nat) (pc next : L) :
    (CounterInstr.inc tmp next).eval (copyState base r q tmp n m z pc) =
      copyState base r q tmp n m (z + 1) next := by
  simp [CounterInstr.eval, copyState]

/-- Copy the consumed value into both destination and restoration scratch. -/
theorem duplicate_counter_run (code : L → CounterInstr R L) (r q tmp : R)
    (hrq : r ≠ q) (hrt : r ≠ tmp) (hqt : q ≠ tmp)
    (loop pop add save stop : L) (hloop : code loop = .branch r stop pop)
    (hpop : code pop = .dec r add) (hadd : code add = .inc q save) (hsave : code save = .inc tmp loop)
    (base : CounterCfg R L) (n m z : Nat) :
    CounterRun code (copyState base r q tmp n m z loop) (4 * n + 1)
      (copyState base r q tmp 0 (m + n) (z + n) stop) := by
  induction n generalizing m z with
  | zero =>
    apply CounterRun.next (code := code) (l := loop) rfl
    simpa [hloop, CounterInstr.eval, copyState, hrq, hrt] using
      CounterRun.refl (copyState base r q tmp 0 m z stop)
  | succ n ih =>
    have h₁ := CounterRun.next (code := code) (l := save)
      (s := copyState base r q tmp n (m + 1) z save) rfl
      (by simpa [hsave] using ih (m + 1) (z + 1))
    have h₂ := CounterRun.next (code := code) (l := add)
      (s := copyState base r q tmp n m z add) rfl
      (by simpa [hadd, copyState_inc_middle base r q tmp hqt] using h₁)
    have h₃ := CounterRun.next (code := code) (l := pop)
      (s := copyState base r q tmp (n + 1) m z pop) rfl
      (by simpa [hpop, copyState_dec base r q tmp hrq hrt hqt] using h₂)
    have h₄ := CounterRun.next (code := code) (l := loop)
      (s := copyState base r q tmp (n + 1) m z loop) rfl
      (by simpa [hloop, CounterInstr.eval, copyState, hrq, hrt] using h₃)
    convert h₄ using 1 <;> simp [copyState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Nonconsuming addition/copy, with restoration scratch returned to zero. -/
theorem copy_counter_run (code : L → CounterInstr R L) (r q tmp : R)
    (hrq : r ≠ q) (hrt : r ≠ tmp) (hqt : q ≠ tmp)
    (loop pop add save restore consume back stop : L)
    (hloop : code loop = .branch r restore pop) (hpop : code pop = .dec r add)
    (hadd : code add = .inc q save) (hsave : code save = .inc tmp loop)
    (hrestore : code restore = .branch tmp stop consume) (hconsume : code consume = .dec tmp back)
    (hback : code back = .inc r restore) (base : CounterCfg R L) (n m : Nat) :
    CounterRun code (copyState base r q tmp n m 0 loop) (7 * n + 2)
      (copyState base r q tmp n (m + n) 0 stop) := by
  have h₁ := duplicate_counter_run code r q tmp hrq hrt hqt loop pop add save restore
    hloop hpop hadd hsave base n m 0
  simp only [Nat.zero_add] at h₁
  let after := copyState base r q tmp 0 (m + n) n restore
  have h₂ := transfer_counter_run code tmp r (Ne.symm hrt) restore consume back stop
    hrestore hconsume hback after n 0
  have hi : transferState after tmp r n 0 restore = after := by
    apply CounterCfg.ext
    · rfl
    · funext j
      by_cases hr : j = r
      · subst j; simp [after, transferState, copyState, hrq, hrt]
      · by_cases ht : j = tmp
        · subst j; simp [after, transferState, copyState, Ne.symm hrt]
        · simp [after, transferState, copyState, hr, ht]
    · rfl
  have ho : transferState after tmp r 0 (0 + n) stop = copyState base r q tmp n (m + n) 0 stop := by
    apply CounterCfg.ext
    · rfl
    · funext j
      by_cases hr : j = r
      · subst j; simp [after, transferState, copyState, hrq, hrt]
      · by_cases ht : j = tmp
        · subst j; simp [after, transferState, copyState, Ne.symm hrt]
        · by_cases hq : j = q
          · subst j; simp [after, transferState, copyState, Ne.symm hrq, hqt]
          · simp [after, transferState, copyState, hr, ht, hq]
    · rfl
  rw [hi, ho] at h₂
  have h := CounterRun.trans (R := R) (L := L) code h₁ h₂
  convert h using 1 <;> omega

end ShiReversibleGenerator
