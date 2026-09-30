import «AMPUNI-piece-controller-work-step»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry ShiTMPieceSchedule

theorem work_copy_mark_step (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hsrc : S (.inr (source atom)) = .mark :: tail) :
    run^[1] (some { l := some (.work copy pc atom table .copy), var := v, stk := S }) =
      some { l := some (.work copy pc atom table .copy), var := some Cell.mark, stk :=
        (Function.update
          (Function.update
            (Function.update S (.inr (source atom)) tail)
            (.inl (.inl (destination table)))
              (.mark :: S (.inl (.inl (destination table)))))
          (.inl (.inl (3 : Fin 14)))
            (.mark :: S (.inl (.inl (3 : Fin 14))))) } := by
  have hstep := work_step_lift copy pc atom table .copy (by decide) v S
  have hold := copy_mark_step_at (source atom) (destination table)
    v S tail (by cases table <;> decide) hsrc
  calc
    _ = (runAt (source atom) (destination table)
          (some { l := some (.inr .copy), var := v, stk := S })).map
            (liftCfg copy pc atom table) := by
          simpa [liftCfg, liftLabel] using hstep
    _ = _ := by
          simpa [liftCfg, liftLabel] using
            congrArg (Option.map (liftCfg copy pc atom table)) hold

theorem work_copy_empty_step (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr (source atom)) = []) :
    run^[1] (some { l := some (.work copy pc atom table .copy), var := v, stk := S }) =
      some { l := some (.work copy pc atom table .restore), var := none, stk := S } := by
  have hstep := work_step_lift copy pc atom table .copy (by decide) v S
  have hold := copy_empty_step_at (source atom) (destination table) v S hsrc
  calc
    _ = (runAt (source atom) (destination table)
          (some { l := some (.inr .copy), var := v, stk := S })).map
            (liftCfg copy pc atom table) := by
          simpa [liftCfg, liftLabel] using hstep
    _ = _ := by
          simpa [liftCfg, liftLabel] using
            congrArg (Option.map (liftCfg copy pc atom table)) hold

theorem work_restore_mark_step (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = .mark :: tail) :
    run^[1] (some { l := some (.work copy pc atom table .restore), var := v, stk := S }) =
      some { l := some (.work copy pc atom table .restore), var := some Cell.mark, stk :=
        (Function.update
          (Function.update S (.inl (.inl (3 : Fin 14))) tail)
          (.inr (source atom)) (.mark :: S (.inr (source atom)))) } := by
  have hstep := work_step_lift copy pc atom table .restore (by decide) v S
  have hold := restore_mark_step_at (source atom) (destination table)
    v S tail hscratch
  calc
    _ = (runAt (source atom) (destination table)
          (some { l := some (.inr .restore), var := v, stk := S })).map
            (liftCfg copy pc atom table) := by
          simpa [liftCfg, liftLabel] using hstep
    _ = _ := by
          simpa [liftCfg, liftLabel] using
            congrArg (Option.map (liftCfg copy pc atom table)) hold

theorem work_restore_empty_step (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    run^[1] (some { l := some (.work copy pc atom table .restore), var := v, stk := S }) =
      some { l := some (.work copy pc atom table .done), var := none, stk := S } := by
  have hstep := work_step_lift copy pc atom table .restore (by decide) v S
  have hold := restore_empty_step_at (source atom) (destination table)
    v S hscratch
  calc
    _ = (runAt (source atom) (destination table)
          (some { l := some (.inr .restore), var := v, stk := S })).map
            (liftCfg copy pc atom table) := by
          simpa [liftCfg, liftLabel] using hstep
    _ = _ := by
          simpa [liftCfg, liftLabel] using
            congrArg (Option.map (liftCfg copy pc atom table)) hold

end ShiTMPieceController
