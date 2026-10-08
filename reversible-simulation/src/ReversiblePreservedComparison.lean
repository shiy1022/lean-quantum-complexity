import ReversibleComparison
import ReversibleMixedArithmetic

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def comparisonCopies (a b ca cb : R) : List (GeneratorOperation R) :=
  [.affine ⟨a, ca, 0, 1⟩, .affine ⟨b, cb, 0, 1⟩]

theorem comparisonCopies_result (a b ca cb : R) (hbc : b ≠ ca) (cs : R → Nat)
    (ha : cs ca = 0) (hb : cs cb = 0) (hacb : ca ≠ cb) :
    operationResult (comparisonCopies a b ca cb) cs =
      Function.update (Function.update cs ca (cs a)) cb (cs b) := by
  simp [comparisonCopies, operationResult, GeneratorOperation.apply, AffineAtom.apply,
    hbc, ha, hb, Ne.symm hacb]

theorem comparisonCopies_steps (a b ca cb : R) (hbc : b ≠ ca) (cs : R → Nat) :
    operationSteps (comparisonCopies a b ca cb) cs = (7 * cs a + 2) + (7 * cs b + 2) := by
  simp [comparisonCopies, operationSteps, GeneratorOperation.steps, GeneratorOperation.apply, AffineAtom.steps,
    AffineAtom.apply, hbc]

theorem comparisonState_zero (cs : R → Nat) (a b : R) (ha : cs a = 0) (hb : cs b = 0)
    (ys : List Bool) (pc : L) :
    comparisonState ⟨none, cs, ys⟩ a b 0 0 pc = ⟨some pc, cs, ys⟩ := by
  apply CounterCfg.ext
  · rfl
  · funext r; by_cases h₁ : r = a <;> by_cases h₂ : r = b <;>
      simp_all [comparisonState]
  · rfl

/-- The two original counters survive; only their temporary copies are consumed. -/
theorem preservedComparison_run (caller : L → CounterInstr R L) (a b ca cb buf tmp : R)
    (le gt : L)
    (hv : ∀ op ∈ comparisonCopies a b ca cb, op.Valid buf tmp)
    (hbt : buf ≠ tmp) (hbc : b ≠ ca) (hcacb : ca ≠ cb)
    (cs : R → Nat) (hca : cs ca = 0) (hcb : cs cb = 0)
    (hb : cs buf = 0) (ht : cs tmp = 0) (ys : List Bool) :
    let copies := comparisonCopies a b ca cb
    let core := comparisonCode caller ca cb le gt
    CounterRun (operationCode copies core buf tmp (.inl 0))
      ⟨some (operationEntry copies (.inl 0)), cs, ys⟩
      (operationSteps copies cs + comparisonSteps (cs a) (cs b))
      ⟨some (operationExit copies (.inr (if cs a ≤ cs b then le else gt))), cs, ys⟩ := by
  let copies := comparisonCopies a b ca cb
  let core := comparisonCode caller ca cb le gt
  let code := operationCode copies core buf tmp (.inl 0)
  have hc := operationCode_run copies core buf tmp (.inl 0) hv hbt cs hb ht ys
  rw [comparisonCopies_result a b ca cb hbc cs hca hcb hcacb] at hc
  have hr := comparisonCode_run caller ca cb hcacb le gt
    ⟨none, cs, ys⟩ (cs a) (cs b)
  rw [comparisonState_zero cs ca cb hca hcb ys] at hr
  have hr' := CounterRun.relabel core code (operationExit copies)
    (operationCode_embed copies core buf tmp (.inl 0)) hr
  change CounterRun code
    ⟨some (operationExit copies (.inl 0)), Function.update (Function.update cs ca (cs a)) cb (cs b), ys⟩
    (comparisonSteps (cs a) (cs b))
    ⟨some (operationExit copies (.inr (if cs a ≤ cs b then le else gt))), cs, ys⟩ at hr'
  exact CounterRun.trans code hc hr'

theorem preservedComparison_clock_bound (left right : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      ((7 * left.eval n + 2) + (7 * right.eval n + 2)) +
        comparisonSteps (left.eval n) (right.eval n) ≤ p.eval n := by
  refine ⟨Polynomial.C 11 * (left + right) + Polynomial.C 7, ?_⟩
  intro n
  have h := comparisonSteps_bound (left.eval n) (right.eval n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end ShiReversibleGenerator
