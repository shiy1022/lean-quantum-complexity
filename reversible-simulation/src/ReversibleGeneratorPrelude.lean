import ReversibleLayoutPrelude
import ReversibleBudgetFragment

set_option autoImplicit false
namespace ShiReversibleGenerator

abbrev GeneratorPreludeLabels (tm : Turing.FinTM2) (c d : Nat) (L : Type) :=
  InitializedBudgetLabel c d (ArithmeticLabels (layoutAtoms tm) L)

def initializedBudgetEmbed {c d : Nat} {L : Type} (l : L) : InitializedBudgetLabel c d L :=
  .inr (.inr (.inr (.inr l)))

theorem initializedBudgetCode_embed {R L : Type} [DecidableEq R]
    (caller : L → CounterInstr R L) (c d : Nat) (r q dst tmp : R) (stop l : L) :
    initializedBudgetCode caller c d r q dst tmp stop (initializedBudgetEmbed l) =
      (caller l).relabel initializedBudgetEmbed := by
  change ((((caller l).relabel Sum.inr).relabel Sum.inr).relabel Sum.inr).relabel Sum.inr = _
  simp only [CounterInstr.relabel_comp]
  rfl

noncomputable def generatorPreludeCode {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr LayoutRegister L) (stop : L) :
    GeneratorPreludeLabels tm c d L → CounterInstr LayoutRegister (GeneratorPreludeLabels tm c d L) :=
  initializedBudgetCode (arithmeticCode (layoutAtoms tm) caller 5 stop) c d 1 0 2 5
    (arithmeticEntry (layoutAtoms tm) stop)

/-- Budget and layout arithmetic are one actual finite instruction graph. -/
theorem generatorPreludeCode_run {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr LayoutRegister L) (stop : L) (n : Nat) (ys : List Bool) :
    CounterRun (generatorPreludeCode tm c d caller stop)
      ⟨some (.inl ()), layoutInitial n 0, ys⟩
      (powerWork (n + c) d + 2 * d + 2 * c + 1 +
        arithmeticSteps (layoutAtoms tm) (layoutInitial n ((n + c) ^ d)))
      ⟨some (initializedBudgetEmbed (arithmeticExit (layoutAtoms tm) stop)),
        arithmeticResult (layoutAtoms tm) (layoutInitial n ((n + c) ^ d)), ys⟩ := by
  let inner := arithmeticCode (layoutAtoms tm) caller 5 stop
  let outer := generatorPreludeCode tm c d caller stop
  let base : CounterCfg LayoutRegister (GeneratorPreludeLabels tm c d L) :=
    ⟨none, fun _ => 0, ys⟩
  have hb := initializedBudgetCode_run inner c d (1 : LayoutRegister) 0 2 5
    (arithmeticEntry (layoutAtoms tm) stop)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) base n
  have hi : multiplyState base 1 0 2 5 0 n 0 (.inl ()) =
      (⟨some (.inl ()), layoutInitial n 0, ys⟩ : CounterCfg LayoutRegister (GeneratorPreludeLabels tm c d L)) := by
    apply CounterCfg.ext
    · rfl
    · funext r; fin_cases r <;> simp [multiplyState, copyState, withCounter, base, layoutInitial]
    · rfl
  have ho : multiplyState base 1 0 2 5 ((n + c) ^ d) n 0
      (initializedBudgetEmbed (arithmeticEntry (layoutAtoms tm) stop)) =
      (⟨some (initializedBudgetEmbed (arithmeticEntry (layoutAtoms tm) stop)),
        layoutInitial n ((n + c) ^ d), ys⟩ : CounterCfg LayoutRegister (GeneratorPreludeLabels tm c d L)) := by
    apply CounterCfg.ext
    · rfl
    · funext r; fin_cases r <;> simp [multiplyState, copyState, withCounter, base, layoutInitial]
    · rfl
  change CounterRun outer (multiplyState base 1 0 2 5 0 n 0 (.inl ()))
    (powerWork (n + c) d + 2 * d + 2 * c + 1)
    (multiplyState base 1 0 2 5 ((n + c) ^ d) n 0
      (initializedBudgetEmbed (arithmeticEntry (layoutAtoms tm) stop))) at hb
  rw [hi, ho] at hb
  have hl := layoutCode_run tm caller stop n ((n + c) ^ d) ys
  have hl' := CounterRun.relabel inner outer initializedBudgetEmbed
    (initializedBudgetCode_embed inner c d 1 0 2 5 (arithmeticEntry (layoutAtoms tm) stop)) hl
  change CounterRun outer
    ⟨some (initializedBudgetEmbed (arithmeticEntry (layoutAtoms tm) stop)), layoutInitial n ((n + c) ^ d), ys⟩
    (arithmeticSteps (layoutAtoms tm) (layoutInitial n ((n + c) ^ d)))
    ⟨some (initializedBudgetEmbed (arithmeticExit (layoutAtoms tm) stop)),
      arithmeticResult (layoutAtoms tm) (layoutInitial n ((n + c) ^ d)), ys⟩ at hl'
  exact CounterRun.trans outer hb hl'

theorem generatorPreludeCode_clock_polynomial (tm : Turing.FinTM2) (c d : Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      powerWork (n + c) d + 2 * d + 2 * c + 1 +
        arithmeticSteps (layoutAtoms tm) (layoutInitial n ((n + c) ^ d)) = p.eval n := by
  obtain ⟨p, hp⟩ := budgetCode_clock_polynomial c d
  obtain ⟨q, hq⟩ := layoutCode_clock_polynomial tm ((Polynomial.X + Polynomial.C c) ^ d)
  refine ⟨p + Polynomial.C 1 + q, ?_⟩
  intro n
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  rw [← hp]
  have h := hq n
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [← h]

end ShiReversibleGenerator
