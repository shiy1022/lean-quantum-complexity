import «AMPUNI-piece-param-machine»
import «AMPUNI-piece-controller-work-local»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceParam

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule
open ShiTMPieceController ShiTMPieceEntry

/-- All local unary-copy steps are inherited exactly: only dispatch, never a
work state, depends on the chosen command list. -/
theorem work_step_eq (commands : List Command) (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (phase : Control) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    runFor commands
      (some { l := some (.work copy pc atom table phase), var := v, stk := S }) =
    ShiTMPieceController.run
      (some { l := some (.work copy pc atom table phase), var := v, stk := S }) := by
  rfl

theorem work_step_transfer (commands : List Command) (copy : Fin 3)
    (pc : PC) (atom : Atom) (table : Table) (phase : Control)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (target : Option (Cfg TopGam ShiTMPieceController.Label Sig))
    (hold : ShiTMPieceController.run^[1]
      (some { l := some (.work copy pc atom table phase), var := v, stk := S }) =
        target) :
    (runFor commands)^[1]
      (some { l := some (.work copy pc atom table phase), var := v, stk := S }) =
        target := by
  simpa only [Function.iterate_one, work_step_eq] using hold

end ShiTMPieceParam
