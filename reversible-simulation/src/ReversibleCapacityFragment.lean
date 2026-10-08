import ReversibleCopyFragment
import ReversibleBudgetFragment

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

@[simp] theorem copyState_budget (base : CounterCfg R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp)
    (k n m v u : Nat) (p pc : L) :
    copyState (multiplyState base r q dst tmp k n m p) r dst tmp v u 0 pc =
      multiplyState base r q dst tmp v n u pc := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases ht : j = tmp
    · subst j; simp [copyState, multiplyState, withCounter]
    · by_cases hd : j = dst
      · subst j; simp [copyState, multiplyState, withCounter, ht]
      · by_cases hr : j = r
        · subst j; simp [copyState, multiplyState, withCounter, hrd, hrt, hrq]
        · by_cases hq : j = q
          · subst j; simp [copyState, multiplyState, withCounter, Ne.symm hrq, ht, hd]
          · simp [copyState, multiplyState, withCounter, ht, hd, hr, hq]
  · rfl

@[simp] theorem copyState_length (base : CounterCfg R L) (r q dst tmp : R)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp)
    (k n m v u : Nat) (p pc : L) :
    copyState (multiplyState base r q dst tmp k n m p) q dst tmp v u 0 pc =
      multiplyState base r q dst tmp k v u pc := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases ht : j = tmp
    · subst j; simp [copyState, multiplyState, withCounter]
    · by_cases hd : j = dst
      · subst j; simp [copyState, multiplyState, withCounter, ht]
      · by_cases hq : j = q
        · subst j; simp [copyState, multiplyState, withCounter, hd, ht]
        · by_cases hr : j = r
          · subst j; simp [copyState, multiplyState, withCounter, hrq, hrd, hrt]
          · simp [copyState, multiplyState, withCounter, ht, hd, hr, hq]
  · rfl

@[simp] theorem multiplyState_set_dst (base : CounterCfg R L) (r q dst tmp : R)
    (hdt : dst ≠ tmp) (k n m v : Nat) (p pc : L) :
    withCounter (multiplyState base r q dst tmp k n m p) dst v pc =
      multiplyState base r q dst tmp k n v pc := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hd : j = dst
    · subst j; simp [withCounter, multiplyState, copyState, hdt]
    · by_cases ht : j = tmp
      · subst j; simp [withCounter, multiplyState, copyState, Ne.symm hdt]
      · simp [withCounter, multiplyState, copyState, hd, ht]
  · rfl

abbrev CapacityLabel (b : Nat) (L : Type) := CopyLabel b (CopyLabel 1 (ConstantLabel 1 L))

def capacityStart (b : Nat) (stop : L) : CapacityLabel b L :=
  copyFrom b (copyFrom 1 (constantFrom 1 stop 0) 0) 0

def capacityCode (code : L → CounterInstr R L) (b : Nat) (r q dst tmp : R) (stop : L) :
    CapacityLabel b L → CounterInstr R (CapacityLabel b L) :=
  copyFragmentCode
    (copyFragmentCode (incrementCode code 1 dst stop) 1 q dst tmp (constantFrom 1 stop 0))
    b r dst tmp (copyFrom 1 (constantFrom 1 stop 0) 0)

/-- Actual finite capacity calculation preserves the budget, raw length and output.
All restoration scratch is zero at the explicit caller continuation. -/
theorem capacityCode_run (code : L → CounterInstr R L) (b : Nat) (r q dst tmp : R) (stop : L)
    (hrq : r ≠ q) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hqd : q ≠ dst) (hqt : q ≠ tmp) (hdt : dst ≠ tmp)
    (base : CounterCfg R (CapacityLabel b L)) (t n : Nat) :
    CounterRun (capacityCode code b r q dst tmp stop)
      (multiplyState base r q dst tmp t n 0 (capacityStart b stop))
      (b * (7 * t + 2) + (7 * n + 2) + 1)
      (multiplyState base r q dst tmp t n (n + b * t + 1) (.inr (.inr (.inr stop)))) := by
  let inc := incrementCode code 1 dst stop
  let add := copyFragmentCode inc 1 q dst tmp (constantFrom 1 stop 0)
  let outer := copyFragmentCode add b r dst tmp (copyFrom 1 (constantFrom 1 stop 0) 0)
  have hb := copyFragmentCode_run add b r dst tmp (copyFrom 1 (constantFrom 1 stop 0) 0)
    hrd hrt hdt (multiplyState base r q dst tmp t n 0 (capacityStart b stop)) t 0
  simp only [copyState_budget base r q dst tmp hrq hrd hrt, Nat.zero_add] at hb
  let ba : CounterCfg R (CopyLabel 1 (ConstantLabel 1 L)) := ⟨none, base.counters, base.output⟩
  have hn := copyFragmentCode_run inc 1 q dst tmp (constantFrom 1 stop 0) hqd hqt hdt
    (multiplyState ba r q dst tmp t 0 0 (copyFrom 1 (constantFrom 1 stop 0) 0)) n (b * t)
  simp only [copyState_length ba r q dst tmp hrq hrd hrt, Nat.one_mul] at hn
  have hn' := CounterRun.relabel add outer Sum.inr (fun _ => rfl) hn
  change CounterRun outer
    (multiplyState base r q dst tmp t n (b * t) (.inr (copyFrom 1 (constantFrom 1 stop 0) 0))) (7 * n + 2)
    (multiplyState base r q dst tmp t n (b * t + n) (.inr (.inr (constantFrom 1 stop 0)))) at hn'
  let bi : CounterCfg R (ConstantLabel 1 L) := ⟨none, base.counters, base.output⟩
  have hi := incrementCode_run code 1 dst stop
    (multiplyState bi r q dst tmp t n 0 (constantFrom 1 stop 0)) (b * t + n)
  simp only [multiplyState_set_dst bi r q dst tmp hdt] at hi
  let f : ConstantLabel 1 L → CapacityLabel b L := fun l => .inr (.inr l)
  have hf : ∀ l, outer (f l) = (inc l).relabel f := by
    intro l
    change ((inc l).relabel Sum.inr).relabel Sum.inr = (inc l).relabel f
    exact CounterInstr.relabel_comp Sum.inr Sum.inr (inc l)
  have hi' := CounterRun.relabel inc outer f hf hi
  change CounterRun outer
    (multiplyState base r q dst tmp t n (b * t + n) (.inr (.inr (constantFrom 1 stop 0)))) 1
    (multiplyState base r q dst tmp t n (b * t + n + 1) (.inr (.inr (.inr stop)))) at hi'
  have h₁ := CounterRun.trans outer hb hn'
  have h₂ := CounterRun.trans outer h₁ hi'
  simpa only [outer, add, inc, capacityCode, capacityStart, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂

theorem capacityCode_clock_polynomial (b : Nat) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      b * (7 * time.eval n + 2) + (7 * n + 2) + 1 = p.eval n := by
  refine ⟨Polynomial.C b * (Polynomial.C 7 * time + Polynomial.C 2) +
    (Polynomial.C 7 * Polynomial.X + Polynomial.C 2) + Polynomial.C 1, ?_⟩
  intro n
  simp

end ShiReversibleGenerator
