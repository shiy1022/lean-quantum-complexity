import «AMPUNI-piece-controller-draft»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceParam

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule
open ShiTMPieceController
open ShiTMPieceEntry

/-- The already-proved controller's work states are independent of its fixed
program. Only dispatch needs a new command list. This variant permits the
terminal tail program to use the same unary-copy machinery. -/
def machineFor (commands : List Command) :
    ShiTMPieceController.Label → Stmt TopGam ShiTMPieceController.Label Sig
  | .dispatch copy pc =>
      match commandAt commands pc.val with
      | none => .goto (fun _ => .finished copy)
      | some (.delimiter table) =>
          .push (.inl (.inl (destination table))) (cst .delim)
            (.goto (fun _ => .dispatch copy (nextPC pc)))
      | some (.add table .one) =>
          .push (.inl (.inl (destination table))) (cst .mark)
            (.goto (fun _ => .dispatch copy (nextPC pc)))
      | some (.add table atom) =>
          .goto (fun _ => .work copy pc atom table .copy)
  | label => ShiTMPieceController.machine label

def runFor (commands : List Command) :
    Option (Cfg TopGam ShiTMPieceController.Label Sig) →
      Option (Cfg TopGam ShiTMPieceController.Label Sig) :=
  fun cf => cf.bind (step (machineFor commands))

theorem work_machine_eq (commands : List Command) (copy : Fin 3)
    (pc : PC) (atom : Atom) (table : Table) (phase : Control) :
    machineFor commands (.work copy pc atom table phase) =
      ShiTMPieceController.machine (.work copy pc atom table phase) := rfl

theorem dispatch_delimiter_step (commands : List Command)
    (copy : Fin 3) (pc : PC) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt commands pc.val = some (.delimiter table)) :
    (runFor commands)^[1]
      (some { l := some (.dispatch copy pc), var := v, stk := S }) =
        some { l := some (.dispatch copy (nextPC pc)), var := v, stk :=
          (Function.update S (.inl (.inl (destination table)))
            (Cell.delim :: S (.inl (.inl (destination table))))) } := by
  simp [runFor, machineFor, hcommand, step, stepAux, cst]

theorem dispatch_one_step (commands : List Command)
    (copy : Fin 3) (pc : PC) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt commands pc.val = some (.add table .one)) :
    (runFor commands)^[1]
      (some { l := some (.dispatch copy pc), var := v, stk := S }) =
        some { l := some (.dispatch copy (nextPC pc)), var := v, stk :=
          (Function.update S (.inl (.inl (destination table)))
            (Cell.mark :: S (.inl (.inl (destination table))))) } := by
  simp [runFor, machineFor, hcommand, step, stepAux, cst]

theorem dispatch_field_step (commands : List Command)
    (copy : Fin 3) (pc : PC) (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt commands pc.val = some (.add table atom))
    (hone : atom ≠ .one) :
    (runFor commands)^[1]
      (some { l := some (.dispatch copy pc), var := v, stk := S }) =
        some { l := some (.work copy pc atom table .copy), var := v, stk := S } := by
  cases atom <;> simp_all [runFor, machineFor, step, stepAux]

theorem work_done_step (commands : List Command)
    (copy : Fin 3) (pc : PC) (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    (runFor commands)^[1]
      (some { l := some (.work copy pc atom table .done), var := v, stk := S }) =
        some { l := some (.dispatch copy (nextPC pc)), var := v, stk := S } := by
  simp [runFor, machineFor, ShiTMPieceController.machine, step, stepAux]

end ShiTMPieceParam
