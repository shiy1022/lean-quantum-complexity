import ReversibleCounterRelabel
import ReversibleCounterMacros

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev ComparisonLabel (L : Type) := Fin 8 ⊕ L

/-- Compare two temporary copies and drain the remainder before dispatching. -/
def comparisonCode (caller : L → CounterInstr R L) (a b : R) (le gt : L) :
    ComparisonLabel L → CounterInstr R (ComparisonLabel L)
  | .inr l => (caller l).relabel Sum.inr
  | .inl j => match j.val with
    | 0 => .branch a (.inl 4) (.inl 1)
    | 1 => .branch b (.inl 6) (.inl 2)
    | 2 => .dec a (.inl 3)
    | 3 => .dec b (.inl 0)
    | 4 => .branch b (.inr le) (.inl 5)
    | 5 => .dec b (.inl 4)
    | 6 => .branch a (.inr gt) (.inl 7)
    | _ => .dec a (.inl 6)

def comparisonState (base : CounterCfg R L) (a b : R) (k n : Nat) (pc : L) : CounterCfg R L :=
  ⟨some pc, Function.update (Function.update base.counters a k) b n, base.output⟩

@[simp] theorem comparisonState_left (base : CounterCfg R L) (a b : R) (hab : a ≠ b)
    (k n v : Nat) (pc next : L) :
    withCounter (comparisonState base a b k n pc) a v next = comparisonState base a b v n next := by
  apply CounterCfg.ext
  · rfl
  · funext r; by_cases ha : r = a <;> by_cases hb : r = b <;>
      simp_all [withCounter, comparisonState]
  · rfl

@[simp] theorem comparisonState_right (base : CounterCfg R L) (a b : R)
    (k n v : Nat) (pc next : L) :
    withCounter (comparisonState base a b k n pc) b v next = comparisonState base a b k v next := by
  apply CounterCfg.ext
  · rfl
  · funext r; by_cases hb : r = b <;> simp [withCounter, comparisonState, hb]
  · rfl

@[simp] theorem comparisonState_dec_left (base : CounterCfg R L) (a b : R) (hab : a ≠ b)
    (k n : Nat) (pc next : L) :
    (CounterInstr.dec a next).eval (comparisonState base a b k n pc) =
      comparisonState base a b (k - 1) n next := by
  change withCounter (comparisonState base a b k n pc) a
    ((comparisonState base a b k n pc).counters a - 1) next = _
  rw [comparisonState_left base a b hab]
  simp [comparisonState, hab]

@[simp] theorem comparisonState_dec_right (base : CounterCfg R L) (a b : R)
    (k n : Nat) (pc next : L) :
    (CounterInstr.dec b next).eval (comparisonState base a b k n pc) =
      comparisonState base a b k (n - 1) next := by
  change withCounter (comparisonState base a b k n pc) b
    ((comparisonState base a b k n pc).counters b - 1) next = _
  rw [comparisonState_right]
  simp [comparisonState]

def comparisonSteps : Nat → Nat → Nat
  | 0, n => 2 * n + 2
  | k + 1, 0 => 2 * (k + 1) + 3
  | k + 1, n + 1 => comparisonSteps k n + 4

/-- Both copied counters are zero on dispatch; all other counters and bytes survive. -/
theorem comparisonCode_run (caller : L → CounterInstr R L) (a b : R) (hab : a ≠ b)
    (le gt : L) (base : CounterCfg R (ComparisonLabel L)) (k n : Nat) :
    CounterRun (comparisonCode caller a b le gt)
      (comparisonState base a b k n (.inl 0)) (comparisonSteps k n)
      (comparisonState base a b 0 0 (.inr (if k ≤ n then le else gt))) := by
  let code := comparisonCode caller a b le gt
  induction k generalizing n with
  | zero =>
      have hc := clear_counter_run code b (.inl 4) (.inl 5) (.inr le) rfl rfl
        (comparisonState base a b 0 0 (.inl 4)) n
      simp only [comparisonState_right] at hc
      have h := CounterRun.next (code := code) (l := .inl 0)
        (s := comparisonState base a b 0 n (.inl 0)) rfl
        (by simpa [code, comparisonCode, comparisonState, CounterInstr.eval, hab, Ne.symm hab] using hc)
      convert h using 1 <;> simp [comparisonSteps] <;> first | rfl | omega
  | succ k ih =>
      cases n with
      | zero =>
          have hc := clear_counter_run code a (.inl 6) (.inl 7) (.inr gt) rfl rfl
            (comparisonState base a b 0 0 (.inl 6)) (k + 1)
          simp only [comparisonState_left base a b hab] at hc
          have h₁ := CounterRun.next (code := code) (l := .inl 1)
            (s := comparisonState base a b (k + 1) 0 (.inl 1)) rfl
            (by simpa [code, comparisonCode, comparisonState, CounterInstr.eval, hab, Ne.symm hab] using hc)
          have h₂ := CounterRun.next (code := code) (l := .inl 0)
            (s := comparisonState base a b (k + 1) 0 (.inl 0)) rfl
            (by simpa [code, comparisonCode, comparisonState, CounterInstr.eval, hab, Ne.symm hab] using h₁)
          convert h₂ using 1 <;> simp [comparisonSteps, Nat.add_assoc] <;> first | rfl | omega
      | succ n =>
          have h₁ := CounterRun.next (code := code) (l := .inl 3)
            (s := comparisonState base a b k (n + 1) (.inl 3)) rfl
            (by simpa [code, comparisonCode] using ih n)
          have h₂ := CounterRun.next (code := code) (l := .inl 2)
            (s := comparisonState base a b (k + 1) (n + 1) (.inl 2)) rfl
            (by simpa [code, comparisonCode, comparisonState_dec_left base a b hab] using h₁)
          have h₃ := CounterRun.next (code := code) (l := .inl 1)
            (s := comparisonState base a b (k + 1) (n + 1) (.inl 1)) rfl
            (by simpa [code, comparisonCode, comparisonState, CounterInstr.eval, hab, Ne.symm hab] using h₂)
          have h₄ := CounterRun.next (code := code) (l := .inl 0)
            (s := comparisonState base a b (k + 1) (n + 1) (.inl 0)) rfl
            (by simpa [code, comparisonCode, comparisonState, CounterInstr.eval, hab, Ne.symm hab] using h₃)
          convert h₄ using 1 <;> simp [comparisonSteps] <;> first | rfl | omega

theorem comparisonSteps_bound (k n : Nat) : comparisonSteps k n ≤ 4 * (k + n) + 3 := by
  induction k generalizing n with
  | zero => simp only [comparisonSteps]; omega
  | succ k ih =>
      cases n with
      | zero => simp only [comparisonSteps]; omega
      | succ n => have h := ih n; simp only [comparisonSteps]; omega

end ShiReversibleGenerator
