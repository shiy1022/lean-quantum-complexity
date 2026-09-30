import «AMPUNI-stage-chain-active-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMStageChain

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem step_of_machine_eq {A : Type}
    (M : A → Stmt TopGam A Sig) (f : A → Label)
    (l : A) (v : Sig) (S : ∀ k, List (TopGam k))
    (hmachine : machine (f l) = liftStmt f (M l)) :
    run (some (liftCfg f { l := some l, var := v, stk := S })) =
      (componentRun M
        (some { l := some l, var := v, stk := S })).map (liftCfg f) := by
  change some (stepAux (machine (f l)) v S) =
    some (liftCfg f (stepAux (M l) v S))
  rw [hmachine, stepAux_liftStmt]

private theorem tail_machine_nonterminal
    (l : ShiTMPieceController.Label)
    (h : l ≠ .finished 0) :
    machine (tailLabel l) =
      liftStmt tailLabel
        (ShiTMPieceParam.machineFor ShiTMPieceSchedule.tailProgram l) := by
  cases l with
  | top l => rfl
  | dispatch copy pc => rfl
  | work copy pc atom table phase => rfl
  | finished copy =>
      fin_cases copy
      · exact (h rfl).elim
      · rfl
      · rfl

theorem tail_run_lift (n : Nat)
    (c d : Cfg TopGam ShiTMPieceController.Label Sig)
    (hd : d.l ≠ none)
    (hrun : (ShiTMPieceParam.runFor ShiTMPieceSchedule.tailProgram)^[n]
      (some c) = some d) :
    run^[n] (some (liftCfg tailLabel c)) =
      some (liftCfg tailLabel d) := by
  apply run_lift_active
    (ShiTMPieceParam.machineFor ShiTMPieceSchedule.tailProgram)
    tailLabel (fun l => l = .finished 0)
  · intro l v S h
    subst l
    rfl
  · intro l v S h
    exact step_of_machine_eq _ _ l v S (tail_machine_nonterminal l h)
  · exact hd
  · exact hrun

def CopyTerminal : ShiTMPieceController.Label → Prop
  | .finished _ => True
  | _ => False

private theorem copy_machine_nonterminal
    (l : ShiTMPieceController.Label)
    (h : ¬ CopyTerminal l) :
    machine (copyLabel l) =
      liftStmt copyLabel (ShiTMPieceController.machine l) := by
  cases l with
  | top l => rfl
  | dispatch copy pc => rfl
  | work copy pc atom table phase => rfl
  | finished copy => exact (h trivial).elim

theorem copy_run_lift (n : Nat)
    (c d : Cfg TopGam ShiTMPieceController.Label Sig)
    (hd : d.l ≠ none)
    (hrun : ShiTMPieceController.run^[n] (some c) = some d) :
    run^[n] (some (liftCfg copyLabel c)) =
      some (liftCfg copyLabel d) := by
  apply run_lift_active ShiTMPieceController.machine
    copyLabel CopyTerminal
  · intro l v S h
    cases l <;> simp [CopyTerminal] at h
    rfl
  · intro l v S h
    exact step_of_machine_eq _ _ l v S (copy_machine_nonterminal l h)
  · exact hd
  · exact hrun

private theorem mirror_machine_nonterminal (p : ShiTMMirrorInit.Phase)
    (h : p ≠ .done) :
    machine (mirrorLabel p) =
      liftStmt mirrorLabel (ShiTMMirrorInit.machine p) := by
  cases p <;> first | rfl | exact (h rfl).elim

theorem mirror_run_lift (n : Nat)
    (c d : Cfg TopGam ShiTMMirrorInit.Phase Sig)
    (hd : d.l ≠ none)
    (hrun : ShiTMMirrorInit.run^[n] (some c) = some d) :
    run^[n] (some (liftCfg mirrorLabel c)) =
      some (liftCfg mirrorLabel d) := by
  apply run_lift_active ShiTMMirrorInit.machine
    mirrorLabel (fun p => p = .done)
  · intro p v S h
    subst p
    rfl
  · intro p v S h
    exact step_of_machine_eq _ _ p v S (mirror_machine_nonterminal p h)
  · exact hd
  · exact hrun

end ShiTMStageChain
