import «AMPUNI-output-header-work-lift»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry

def copyUpdate (atom : Atom) (S : ∀ k, List (TopGam k))
    (tail : List Cell) : ∀ k, List (TopGam k) :=
  Function.update
    (Function.update
      (Function.update S (.inr (source atom)) tail)
      (.inl (.inl (13 : Fin 14)))
        (.mark :: S (.inl (.inl (13 : Fin 14)))))
    (.inl (.inl (3 : Fin 14)))
      (.mark :: S (.inl (.inl (3 : Fin 14))))

def restoreUpdate (atom : Atom) (S : ∀ k, List (TopGam k))
    (tail : List Cell) : ∀ k, List (TopGam k) :=
  Function.update
    (Function.update S (.inl (.inl (3 : Fin 14))) tail)
    (.inr (source atom)) (.mark :: S (.inr (source atom)))

theorem work_copy_mark_step (pc : PC) (atom : Atom) (v : Sig)
    (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hsrc : S (.inr (source atom)) = .mark :: tail) :
    run^[1]
      (some { l := some (.work pc atom .copy), var := v, stk := S }) =
        some { l := some (.work pc atom .copy), var := some Cell.mark, stk := copyUpdate atom S tail } := by
  have hs := copy_mark_step_at (source atom) (13 : Fin 14)
    v S tail (by decide) hsrc
  rw [show run^[1] (some { l := some (.work pc atom .copy), var := v, stk := S }) =
      (runAt (source atom) (13 : Fin 14)
        (some { l := some (.inr .copy), var := v, stk := S })).map
          (workCfg pc atom) by
    simpa only [Function.iterate_one] using
      work_step pc atom .copy (by decide) v S]
  simpa [workCfg, workLabel, copyUpdate] using
    congrArg (Option.map (workCfg pc atom)) hs

theorem work_copy_empty_step (pc : PC) (atom : Atom) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr (source atom)) = []) :
    run^[1]
      (some { l := some (.work pc atom .copy), var := v, stk := S }) =
        some { l := some (.work pc atom .restore), var := none, stk := S } := by
  have hs := copy_empty_step_at (source atom) (13 : Fin 14) v S hsrc
  rw [show run^[1] (some { l := some (.work pc atom .copy), var := v, stk := S }) =
      (runAt (source atom) (13 : Fin 14)
        (some { l := some (.inr .copy), var := v, stk := S })).map
          (workCfg pc atom) by
    simpa only [Function.iterate_one] using
      work_step pc atom .copy (by decide) v S]
  simpa [workCfg, workLabel] using congrArg (Option.map (workCfg pc atom)) hs

theorem work_restore_mark_step (pc : PC) (atom : Atom) (v : Sig)
    (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = .mark :: tail) :
    run^[1]
      (some { l := some (.work pc atom .restore), var := v, stk := S }) =
        some { l := some (.work pc atom .restore), var := some Cell.mark, stk := restoreUpdate atom S tail } := by
  have hs := restore_mark_step_at (source atom) (13 : Fin 14)
    v S tail hscratch
  rw [show run^[1] (some { l := some (.work pc atom .restore), var := v, stk := S }) =
      (runAt (source atom) (13 : Fin 14)
        (some { l := some (.inr .restore), var := v, stk := S })).map
          (workCfg pc atom) by
    simpa only [Function.iterate_one] using
      work_step pc atom .restore (by decide) v S]
  simpa [workCfg, workLabel, restoreUpdate] using
    congrArg (Option.map (workCfg pc atom)) hs

theorem work_restore_empty_step (pc : PC) (atom : Atom) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    run^[1]
      (some { l := some (.work pc atom .restore), var := v, stk := S }) =
        some { l := some (.work pc atom .done), var := none, stk := S } := by
  have hs := restore_empty_step_at (source atom) (13 : Fin 14) v S hscratch
  rw [show run^[1] (some { l := some (.work pc atom .restore), var := v, stk := S }) =
      (runAt (source atom) (13 : Fin 14)
        (some { l := some (.inr .restore), var := v, stk := S })).map
          (workCfg pc atom) by
    simpa only [Function.iterate_one] using
      work_step pc atom .restore (by decide) v S]
  simpa [workCfg, workLabel] using congrArg (Option.map (workCfg pc atom)) hs

end ShiTMOutputHeader
