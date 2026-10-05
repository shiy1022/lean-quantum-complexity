import «AMPUNI-retained-top-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMRetainedTop

def liftCfg (H : Fin 4 → List ShiTMLayoutMachine.Cell)
    (c : Cfg ShiTMOuterLift.OuterGam ShiTMOuterLift.OuterLabel ShiTMLayoutMachine.Sig) :
    Cfg TopGam TopLabel ShiTMLayoutMachine.Sig :=
  { l := c.l.map Sum.inl, var := c.var, stk := topStacks c.stk H }

private theorem topStacks_update
    (S : ∀ k, List (ShiTMOuterLift.OuterGam k))
    (H : Fin 4 → List ShiTMLayoutMachine.Cell)
    (k : ShiTMOuterLift.OuterK) (v : List (ShiTMOuterLift.OuterGam k)) :
    Function.update (topStacks S H) (Sum.inl k) v =
      topStacks (Function.update S k v) H := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst h
        simp [topStacks]
      · have hs : (Sum.inl j : TopK) ≠ Sum.inl k := by
          intro e
          exact h (Sum.inl.inj e)
        rw [Function.update_of_ne hs]
        change S j = Function.update S k v j
        rw [Function.update_of_ne h]
  | inr j =>
      have hs : (Sum.inr j : TopK) ≠ Sum.inl k := by simp
      rw [Function.update_of_ne hs]
      rfl

theorem stepAux_liftNestedStmt
    (q : Stmt ShiTMOuterLift.OuterGam ShiTMOuterLift.OuterLabel
      ShiTMLayoutMachine.Sig)
    (v : ShiTMLayoutMachine.Sig)
    (S : ∀ k, List (ShiTMOuterLift.OuterGam k))
    (H : Fin 4 → List ShiTMLayoutMachine.Cell) :
    stepAux (liftNestedStmt q) v (topStacks S H) =
      liftCfg H (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [liftNestedStmt, stepAux]
      rw [topStacks_update]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      simp only [liftNestedStmt, stepAux, topStacks]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [liftNestedStmt, stepAux, topStacks]
      rw [topStacks_update]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      simp only [liftNestedStmt, stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [liftNestedStmt, stepAux]
      cases h : f v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem step_lift (H : Fin 4 → List ShiTMLayoutMachine.Cell)
    (c : Cfg ShiTMOuterLift.OuterGam ShiTMOuterLift.OuterLabel
      ShiTMLayoutMachine.Sig) :
    step topMachine (liftCfg H c) =
      (step ShiTMOuterLift.nestedMachine c).map (liftCfg H) := by
  cases c with
  | mk l v S =>
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (liftNestedStmt (ShiTMOuterLift.nestedMachine l))
            v (topStacks S H)) =
            some (liftCfg H (stepAux (ShiTMOuterLift.nestedMachine l) v S))
          rw [stepAux_liftNestedStmt]

theorem topRun_lift (H : Fin 4 → List ShiTMLayoutMachine.Cell)
    (cf : Option (Cfg ShiTMOuterLift.OuterGam ShiTMOuterLift.OuterLabel
      ShiTMLayoutMachine.Sig)) :
    topRun (cf.map (liftCfg H)) =
      (ShiTMOuterLift.nestedRun cf).map (liftCfg H) := by
  cases cf with
  | none => rfl
  | some c =>
      simp only [Option.map_some, topRun, ShiTMOuterLift.nestedRun, Option.bind_some]
      exact step_lift H c

/-- Every nested circuit run lifts unchanged into the new top-level machine; the four
retained header stacks are a frame throughout the whole circuit computation. -/
theorem topRun_iter_lift (H : Fin 4 → List ShiTMLayoutMachine.Cell) (n : Nat)
    (cf : Option (Cfg ShiTMOuterLift.OuterGam ShiTMOuterLift.OuterLabel
      ShiTMLayoutMachine.Sig)) :
    topRun^[n] (cf.map (liftCfg H)) =
      (ShiTMOuterLift.nestedRun^[n] cf).map (liftCfg H) := by
  induction n generalizing cf with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [topRun_lift]
      exact ih (ShiTMOuterLift.nestedRun cf)

end ShiTMRetainedTop
