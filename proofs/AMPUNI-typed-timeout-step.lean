import «AMPUNI-typed-timeout-skeleton»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMTypedTimeout

private theorem liftStk_update {K : Type} [DecidableEq K]
    {Gam : K → Type} (fuel : List Bool) (S : ∀ k, List (Gam k))
    (k : K) (v : List (Gam k)) :
    Function.update (liftStk fuel S) (Sum.inl k) v =
      liftStk fuel (Function.update S k v) := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst h
        simp [liftStk]
      · have hs : (Sum.inl j : ClockK K) ≠ Sum.inl k := by
          intro e
          exact h (Sum.inl.inj e)
        rw [Function.update_of_ne hs]
        change S j = Function.update S k v j
        rw [Function.update_of_ne h]
  | inr u =>
      have h : (Sum.inr u : ClockK K) ≠ Sum.inl k := by simp
      rw [Function.update_of_ne h]
      rfl

/-- A translated typed-alphabet statement preserves the source step exactly;
only its control label and a Boolean clock flag are added. -/
theorem stepAux_clockStmt {K L sig : Type} [DecidableEq K]
    {Gam : K → Type} (q : Stmt Gam L sig) (v : sig)
    (S : ∀ k, List (Gam k)) (fuel : List Bool) :
    stepAux (clockStmt q) (v, true) (liftStk fuel S) =
      liftCfg fuel (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [clockStmt, stepAux]
      rw [liftStk_update]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simp only [clockStmt, stepAux, liftStk]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [clockStmt, stepAux, liftStk]
      rw [liftStk_update]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      simp only [clockStmt, stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [clockStmt, stepAux]
      cases h : f v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

end ShiTMTypedTimeout
