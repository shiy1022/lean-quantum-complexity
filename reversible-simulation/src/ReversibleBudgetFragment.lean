import ReversiblePowerFragment
import ReversibleConstantFragment

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L L' L'' : Type} [DecidableEq R]

@[simp] theorem CounterInstr.relabel_comp (f : L → L') (g : L' → L'') (instr : CounterInstr R L) :
    (instr.relabel f).relabel g = instr.relabel (g ∘ f) := by
  cases instr <;> rfl

@[simp] theorem multiplyState_relabel (f : L → L') (base : CounterCfg R L)
    (r q dst tmp : R) (k n m : Nat) (pc : L) :
    (multiplyState base r q dst tmp k n m pc).relabel f =
      multiplyState (base.relabel f) r q dst tmp k n m (f pc) := rfl

@[simp] theorem withCounter_relabel (f : L → L') (base : CounterCfg R L) (r : R) (n : Nat) (pc : L) :
    (withCounter base r n pc).relabel f = withCounter (base.relabel f) r n (f pc) := rfl

@[simp] theorem multiplyState_set_q (base : CounterCfg R L) (r q dst tmp : R)
    (hqd : q ≠ dst) (hqt : q ≠ tmp) (k n m v : Nat) (p pc : L) :
    withCounter (multiplyState base r q dst tmp k n m p) q v pc =
      multiplyState base r q dst tmp k v m pc := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hq : j = q
    · subst j; simp [withCounter, multiplyState, copyState, hqd, hqt]
    · by_cases ht : j = tmp
      · subst j; simp [withCounter, multiplyState, copyState, Ne.symm hqt]
      · by_cases hd : j = dst
        · subst j; simp [withCounter, multiplyState, copyState, Ne.symm hqd, ht]
        · simp [withCounter, multiplyState, copyState, hq, ht, hd]
  · rfl

abbrev BudgetLabel (c d : Nat) (L : Type) := ConstantLabel c (FragmentLabel d (ConstantLabel c L))

def budgetStart (c d : Nat) (stop : L) : BudgetLabel c d L :=
  constantFrom c (fragmentFrom d (constantFrom c stop 0) 0) 0

def budgetCode (code : L → CounterInstr R L) (c d : Nat) (r q dst tmp : R) (stop : L) :
    BudgetLabel c d L → CounterInstr R (BudgetLabel c d L) :=
  incrementCode
    (fragmentCode (decrementCode code c q stop) d r q dst tmp (constantFrom c stop 0))
    c q (fragmentFrom d (constantFrom c stop 0) 0)

/-- The actual finite prelude computes a shifted-power budget and restores the raw length.
It returns to caller code with zero scratch, preserving all other registers and output. -/
theorem budgetCode_run (code : L → CounterInstr R L) (c d : Nat) (r q dst tmp : R) (stop : L)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (base : CounterCfg R (BudgetLabel c d L)) (n : Nat) :
    CounterRun (budgetCode code c d r q dst tmp stop)
      (multiplyState base r q dst tmp 1 n 0 (budgetStart c d stop))
      (powerWork (n + c) d + 2 * d + 2 * c)
      (multiplyState base r q dst tmp ((n + c) ^ d) n 0 (.inr (.inr (.inr stop)))) := by
  let dec := decrementCode code c q stop
  let pow := fragmentCode dec d r q dst tmp (constantFrom c stop 0)
  let outer := incrementCode pow c q (fragmentFrom d (constantFrom c stop 0) 0)
  have hi := incrementCode_run pow c q (fragmentFrom d (constantFrom c stop 0) 0)
    (multiplyState base r q dst tmp 1 0 0 (budgetStart c d stop)) n
  simp only [multiplyState_set_q base r q dst tmp hqd hqt] at hi
  let bp : CounterCfg R (FragmentLabel d (ConstantLabel c L)) := ⟨none, base.counters, base.output⟩
  have hp := fragmentCode_run dec d r q dst tmp (constantFrom c stop 0)
    hrq hrd hrt hqd hqt hdt bp 1 (n + c)
  simp only [Nat.one_mul] at hp
  have hp' := CounterRun.relabel pow outer Sum.inr (fun _ => rfl) hp
  simp only [multiplyState_relabel] at hp'
  change CounterRun outer
    (multiplyState base r q dst tmp 1 (n + c) 0 (.inr (fragmentFrom d (constantFrom c stop 0) 0)))
    (powerWork (n + c) d + 2 * d)
    (multiplyState base r q dst tmp ((n + c) ^ d) (n + c) 0 (.inr (.inr (constantFrom c stop 0)))) at hp'
  let bd : CounterCfg R (ConstantLabel c L) := ⟨none, base.counters, base.output⟩
  have hd := decrementCode_run code c q stop
    (multiplyState bd r q dst tmp ((n + c) ^ d) 0 0 (constantFrom c stop 0)) n
  simp only [multiplyState_set_q bd r q dst tmp hqd hqt] at hd
  let f : ConstantLabel c L → BudgetLabel c d L := fun l => .inr (.inr l)
  have hf : ∀ l, outer (f l) = (dec l).relabel f := by
    intro l
    change ((dec l).relabel Sum.inr).relabel Sum.inr = (dec l).relabel f
    exact CounterInstr.relabel_comp Sum.inr Sum.inr (dec l)
  have hd' := CounterRun.relabel dec outer f hf hd
  simp only [multiplyState_relabel] at hd'
  change CounterRun outer
    (multiplyState base r q dst tmp ((n + c) ^ d) (n + c) 0 (.inr (.inr (constantFrom c stop 0)))) c
    (multiplyState base r q dst tmp ((n + c) ^ d) n 0 (.inr (.inr (.inr stop)))) at hd'
  have h₁ := CounterRun.trans outer hi hp'
  have h₂ := CounterRun.trans outer h₁ hd'
  simpa only [outer, pow, dec, budgetCode, budgetStart, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using h₂

/-- The prelude's actual instruction count is one fixed polynomial in raw input length. -/
theorem budgetCode_clock_polynomial (c d : Nat) :
    ∃ p : Polynomial Nat, ∀ n, powerWork (n + c) d + 2 * d + 2 * c = p.eval n := by
  refine ⟨(powerWorkPolynomial d).comp (Polynomial.X + Polynomial.C c) + Polynomial.C (2 * d + 2 * c), ?_⟩
  intro n
  simp [Polynomial.eval_comp, Nat.add_assoc]

@[simp] theorem multiplyState_inc (base : CounterCfg R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (k n m : Nat) (pc next : L) :
    (CounterInstr.inc r next).eval (multiplyState base r q dst tmp k n m pc) =
      multiplyState base r q dst tmp (k + 1) n m next := by
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

abbrev InitializedBudgetLabel (c d : Nat) (L : Type) := Unit ⊕ BudgetLabel c d L

def initializedBudgetCode (code : L → CounterInstr R L) (c d : Nat) (r q dst tmp : R) (stop : L) :
    InitializedBudgetLabel c d L → CounterInstr R (InitializedBudgetLabel c d L)
  | .inl _ => .inc r (.inr (budgetStart c d stop))
  | .inr l => (budgetCode code c d r q dst tmp stop l).relabel Sum.inr

/-- The generator can start this concrete finite prelude with all work counters zero. -/
theorem initializedBudgetCode_run (code : L → CounterInstr R L) (c d : Nat) (r q dst tmp : R) (stop : L)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (base : CounterCfg R (InitializedBudgetLabel c d L)) (n : Nat) :
    CounterRun (initializedBudgetCode code c d r q dst tmp stop)
      (multiplyState base r q dst tmp 0 n 0 (.inl ()))
      (powerWork (n + c) d + 2 * d + 2 * c + 1)
      (multiplyState base r q dst tmp ((n + c) ^ d) n 0 (.inr (.inr (.inr (.inr stop))))) := by
  let b : CounterCfg R (BudgetLabel c d L) := ⟨none, base.counters, base.output⟩
  have h := budgetCode_run code c d r q dst tmp stop hrq hrd hrt hqd hqt hdt b n
  have h' := CounterRun.relabel (budgetCode code c d r q dst tmp stop)
    (initializedBudgetCode code c d r q dst tmp stop) Sum.inr (fun _ => rfl) h
  simp only [multiplyState_relabel] at h'
  change CounterRun (initializedBudgetCode code c d r q dst tmp stop)
    (multiplyState base r q dst tmp 1 n 0 (.inr (budgetStart c d stop)))
    (powerWork (n + c) d + 2 * d + 2 * c)
    (multiplyState base r q dst tmp ((n + c) ^ d) n 0 (.inr (.inr (.inr (.inr stop))))) at h'
  apply CounterRun.next (l := .inl ()) rfl
  simpa only [initializedBudgetCode, multiplyState_inc base r q dst tmp hrq hrd hrt, Nat.zero_add] using h'

end ShiReversibleGenerator
