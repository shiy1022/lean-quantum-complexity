import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Tactic

set_option autoImplicit false

namespace ShiReversibleTM

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- A syntactic upper bound on pushes in one fixed TM2 statement tree. -/
def pushBound : Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_stack_length (q : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (i : K) :
    ((Turing.TM2.stepAux q v S).stk i).length ≤ (S i).length + pushBound q := by
  induction q generalizing v S with
  | push k f q ih =>
    have h := ih v (Function.update S k (f v :: S k))
    by_cases hi : i = k
    · subst i
      simpa [Turing.TM2.stepAux, pushBound, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h
    · simp only [Function.update_of_ne hi] at h
      simp only [Turing.TM2.stepAux, pushBound]
      omega
  | peek k f q ih => exact ih (f v (S k).head?) S
  | pop k f q ih =>
    have h := ih (f v (S k).head?) (Function.update S k (S k).tail)
    by_cases hi : i = k
    · subst i
      simp only [Function.update_self, List.length_tail] at h
      simp only [Turing.TM2.stepAux, pushBound]
      omega
    · simpa [Turing.TM2.stepAux, pushBound, Function.update_of_ne hi] using h
  | load f q ih => exact ih (f v) S
  | branch f q r ihq ihr =>
    cases hf : f v
    · have h := ihr v S
      simp only [Turing.TM2.stepAux, hf, Bool.cond_false, pushBound]
      exact h.trans (Nat.add_le_add_left (le_max_right _ _) _)
    · have h := ihq v S
      simp only [Turing.TM2.stepAux, hf, Bool.cond_true, pushBound]
      exact h.trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp [Turing.TM2.stepAux, pushBound]
  | halt => simp [Turing.TM2.stepAux, pushBound]

end ShiReversibleTM
