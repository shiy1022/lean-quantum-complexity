import «AMPUNI-replay-cycle-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayCycle

open ShiTMLayoutMachine ShiTMRetainedTop

def liftCfg {A : Type} (f : A → CycleLabel)
    (c : Cfg TopGam A Sig) : Cfg TopGam CycleLabel Sig :=
  { l := c.l.map f, var := c.var, stk := c.stk }

theorem stepAux_liftStmt {A : Type} (f : A → CycleLabel)
    (q : Stmt TopGam A Sig) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    stepAux (liftStmt f q) v S = liftCfg f (stepAux q v S) := by
  induction q generalizing v S with
  | push k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih v (Function.update S k (g v :: S k))
  | peek k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v (S k).head?) S
  | pop k g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v (S k).head?) (Function.update S k (S k).tail)
  | load g q ih =>
      simp only [liftStmt, stepAux]
      exact ih (g v) S
  | branch g q₁ q₂ ih₁ ih₂ =>
      simp only [liftStmt, stepAux]
      cases h : g v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto g => rfl
  | halt => rfl

theorem split_false_step (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (splitLabel false), v, S⟩) =
      (ShiTMReplayMarkSplit.run (some ⟨some false, v, S⟩)).map
        (liftCfg splitLabel) := by
  change some (stepAux
    (liftStmt splitLabel (ShiTMReplayMarkSplit.machine false)) v S) =
      some (liftCfg splitLabel
        (stepAux (ShiTMReplayMarkSplit.machine false) v S))
  exact congrArg some (stepAux_liftStmt splitLabel
    (ShiTMReplayMarkSplit.machine false) v S)

theorem reload_zero_step (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (reloadLabel 0), v, S⟩) =
      (ShiTMReplayReload.run
        (some ⟨some (0 : ShiTMReplayReload.ReloadLabel), v, S⟩)).map
        (liftCfg reloadLabel) := by
  change some (stepAux
    (liftStmt reloadLabel (ShiTMReplayReload.machine 0)) v S) =
      some (liftCfg reloadLabel
        (stepAux (ShiTMReplayReload.machine 0) v S))
  exact congrArg some (stepAux_liftStmt reloadLabel
    (ShiTMReplayReload.machine 0) v S)

theorem reload_one_step (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (reloadLabel 1), v, S⟩) =
      (ShiTMReplayReload.run
        (some ⟨some (1 : ShiTMReplayReload.ReloadLabel), v, S⟩)).map
        (liftCfg reloadLabel) := by
  change some (stepAux
    (liftStmt reloadLabel (ShiTMReplayReload.machine 1)) v S) =
      some (liftCfg reloadLabel
        (stepAux (ShiTMReplayReload.machine 1) v S))
  exact congrArg some (stepAux_liftStmt reloadLabel
    (ShiTMReplayReload.machine 1) v S)

theorem restore_false_step (v : Sig) (S : ∀ k, List (TopGam k)) :
    run (some ⟨some (restoreLabel false), v, S⟩) =
      (ShiTMReplayMarkRestore.run (some ⟨some false, v, S⟩)).map
        (liftCfg restoreLabel) := by
  change some (stepAux
    (liftStmt restoreLabel (ShiTMReplayMarkRestore.machine false)) v S) =
      some (liftCfg restoreLabel
        (stepAux (ShiTMReplayMarkRestore.machine false) v S))
  exact congrArg some (stepAux_liftStmt restoreLabel
    (ShiTMReplayMarkRestore.machine false) v S)

end ShiTMReplayCycle
