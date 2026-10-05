import «AMPUNI-stack-frame»
import «AMPUNI-retained-top-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMTopFrame

open ShiTMRetainedTop ShiTMOuterLift ShiTMLayoutMachine
variable {L sig : Type}
abbrev extendStacks := topStacks

def cfg (A : Fin 4 → List Cell) (c : Cfg OuterGam L sig) : Cfg TopGam L sig :=
  ⟨c.l, c.var, extendStacks c.stk A⟩

def stmt : Stmt OuterGam L sig → Stmt TopGam L sig
  | .push k f q => .push (.inl k) f (stmt q)
  | .peek k f q => .peek (.inl k) f (stmt q)
  | .pop k f q => .pop (.inl k) f (stmt q)
  | .load f q => .load f (stmt q)
  | .branch f a b => .branch f (stmt a) (stmt b)
  | .goto f => .goto f
  | .halt => .halt

private theorem stacks_update (S : ∀ k, List (OuterGam k)) (A : Fin 4 → List Cell)
    (k : OuterK) (s : List (OuterGam k)) :
    Function.update (extendStacks S A) (.inl k) s =
      extendStacks (Function.update S k s) A := by
  funext j
  cases j with
  | inl j =>
      by_cases hj : j = k
      · subst j; simp [extendStacks, topStacks]
      · have hne : (Sum.inl j : TopK) ≠ .inl k := by simpa using hj
        simp [extendStacks, topStacks, hj, hne]
  | inr j => simp [extendStacks, topStacks]

theorem stepAux_stmt (q : Stmt OuterGam L sig) (v : sig)
    (S : ∀ k, List (OuterGam k)) (A : Fin 4 → List Cell) :
    stepAux (stmt q) v (extendStacks S A) = cfg A (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [stmt, stepAux]
      rw [stacks_update]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [stmt, stepAux, extendStacks]
      rw [stacks_update]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih (f v) S
  | branch f a b iha ihb =>
      simp only [stmt, stepAux]
      cases f v
      · exact ihb v S
      · exact iha v S
  | goto f => rfl
  | halt => rfl

def machine (M : L → Stmt OuterGam L sig) : L → Stmt TopGam L sig :=
  fun l => stmt (M l)

open ShiTMStackFrame (run)

/-- Every step preserves an arbitrary family of added stacks, with no
assumption on their contents or on the source machine's control flow. -/
theorem run_frame (M : L → Stmt OuterGam L sig) (A : Fin 4 → List Cell)
    (c : Option (Cfg OuterGam L sig)) :
    run (machine M) (c.map (cfg A)) = (run M c).map (cfg A) := by
  cases c with
  | none => rfl
  | some c =>
      cases c with
      | mk l v S =>
          cases l with
          | none => rfl
          | some l =>
              change some (stepAux (stmt (M l)) v (extendStacks S A)) =
                some (cfg A (stepAux (M l) v S))
              rw [stepAux_stmt]

/-- Whole-run lifting preserves the exact source step count and all added
stacks. This includes halted runs, not only paths ending at active labels. -/
theorem run_iter_frame (M : L → Stmt OuterGam L sig) (A : Fin 4 → List Cell)
    (n : Nat) (c : Option (Cfg OuterGam L sig)) :
    (run (machine M))^[n] (c.map (cfg A)) =
      ((run M)^[n] c).map (cfg A) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, run_frame]
      exact ih (run M c)

end ShiTMTopFrame
