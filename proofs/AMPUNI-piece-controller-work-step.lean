import «AMPUNI-piece-controller-lift»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry ShiTMPieceSchedule

/-- A nonterminal controller work state takes exactly the corresponding step
of the retained-field unary-copy machine, with only its label relabeled. -/
theorem work_step_lift (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (phase : Control)
    (hphase : phase ≠ .done) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run (some (liftCfg copy pc atom table
      { l := some (.inr phase), var := v, stk := S })) =
      (runAt (source atom) (destination table)
        (some { l := some (.inr phase), var := v, stk := S })).map
          (liftCfg copy pc atom table) := by
  cases phase with
  | start =>
      simp [run, runAt, step, machine, liftCfg, liftLabel,
        stepAux_liftEntryStmt]
  | copy =>
      simp [run, runAt, step, machine, liftCfg, liftLabel,
        stepAux_liftEntryStmt]
  | restore =>
      simp [run, runAt, step, machine, liftCfg, liftLabel,
        stepAux_liftEntryStmt]
  | done => exact (hphase rfl).elim

end ShiTMPieceController
