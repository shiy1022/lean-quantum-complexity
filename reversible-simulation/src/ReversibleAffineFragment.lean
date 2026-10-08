import ReversibleCopyFragment
import ReversibleBudgetFragment
import ReversibleMachineEncoding

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

@[simp] theorem copyState_set_dst (base : CounterCfg R L) (r dst tmp : R) (hdt : dst ≠ tmp)
    (n m v : Nat) (p pc : L) :
    withCounter (copyState base r dst tmp n m 0 p) dst v pc = copyState base r dst tmp n v 0 pc := by
  apply CounterCfg.ext
  · rfl
  · funext j
    by_cases hd : j = dst
    · subst j; simp [withCounter, copyState, hdt]
    · by_cases ht : j = tmp
      · subst j; simp [withCounter, copyState, Ne.symm hdt]
      · simp [withCounter, copyState, hd, ht]
  · rfl

abbrev AffineLabel (a b : Nat) (L : Type) := CopyLabel b (ConstantLabel a L)

def affineStart (a b : Nat) (stop : L) : AffineLabel a b L := copyFrom b (constantFrom a stop 0) 0

def affineCode (code : L → CounterInstr R L) (a b : Nat) (r dst tmp : R) (stop : L) :
    AffineLabel a b L → CounterInstr R (AffineLabel a b L) :=
  copyFragmentCode (incrementCode code a dst stop) b r dst tmp (constantFrom a stop 0)

/-- Fixed-coefficient affine arithmetic as actual finite instructions, preserving its argument. -/
theorem affineCode_run (code : L → CounterInstr R L) (a b : Nat) (r dst tmp : R) (stop : L)
    (hrd : r ≠ dst) (hrt : r ≠ tmp) (hdt : dst ≠ tmp)
    (base : CounterCfg R (AffineLabel a b L)) (n m : Nat) :
    CounterRun (affineCode code a b r dst tmp stop)
      (copyState base r dst tmp n m 0 (affineStart a b stop)) (b * (7 * n + 2) + a)
      (copyState base r dst tmp n (m + b * n + a) 0 (.inr (.inr stop))) := by
  let inc := incrementCode code a dst stop
  let outer := copyFragmentCode inc b r dst tmp (constantFrom a stop 0)
  have hb := copyFragmentCode_run inc b r dst tmp (constantFrom a stop 0) hrd hrt hdt base n m
  let bi : CounterCfg R (ConstantLabel a L) := ⟨none, base.counters, base.output⟩
  have hi := incrementCode_run code a dst stop (copyState bi r dst tmp n 0 0 (constantFrom a stop 0)) (m + b * n)
  simp only [copyState_set_dst bi r dst tmp hdt] at hi
  have hi' := CounterRun.relabel inc outer Sum.inr (fun _ => rfl) hi
  change CounterRun outer
    (copyState base r dst tmp n (m + b * n) 0 (.inr (constantFrom a stop 0))) a
    (copyState base r dst tmp n (m + b * n + a) 0 (.inr (.inr stop))) at hi'
  have h := CounterRun.trans outer hb hi'
  simpa only [outer, inc, affineCode, affineStart] using h

theorem affineCode_clock_polynomial (a b : Nat) (size : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n, b * (7 * size.eval n + 2) + a = p.eval n := by
  refine ⟨Polynomial.C b * (Polynomial.C 7 * size + Polynomial.C 2) + Polynomial.C a, ?_⟩
  intro n
  simp

/-- The computed width is exactly the existing configuration codec's width. -/
theorem configurationWidth_fragment (tm : Turing.FinTM2) (code : L → CounterInstr R L)
    (r dst tmp : R) (stop : L) (hrd : r ≠ dst) (hrt : r ≠ tmp) (hdt : dst ≠ tmp) :
    ∃ a b : Nat, (∀ cap, ShiReversibleTM.configurationWidth tm cap = b * cap + a) ∧
      ∀ (base : CounterCfg R (AffineLabel a b L)) (cap : Nat),
        CounterRun (affineCode code a b r dst tmp stop)
          (copyState base r dst tmp cap 0 0 (affineStart a b stop)) (b * (7 * cap + 2) + a)
          (copyState base r dst tmp cap (ShiReversibleTM.configurationWidth tm cap) 0 (.inr (.inr stop))) := by
  obtain ⟨b, a, hw⟩ := ShiReversibleTM.configurationWidth_affine tm
  refine ⟨a, b, hw, ?_⟩
  intro base cap
  simpa only [Nat.zero_add, hw cap] using affineCode_run code a b r dst tmp stop hrd hrt hdt base cap 0

end ShiReversibleGenerator
