import «AMPUNI-piece-entry-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

/-- The same finite program with a selectable retained source and layout destination.
Layout stack 3 remains the temporary scratch stack. -/
def machineAt (source : Fin 4) (dest : Fin 14) : EntryLabel →
    Stmt TopGam EntryLabel Sig
  | .inl l => liftTopStmt (topMachine l)
  | .inr .start =>
      .push (.inl (.inl dest)) (cst .delim)
        (.goto (fun _ => .inr .copy))
  | .inr .copy =>
      .pop (.inr source) pop
        (.branch isMark
          (.push (.inl (.inl dest)) (cst .mark)
            (.push (.inl (.inl (3 : Fin 14))) (cst .mark)
              (.goto (fun _ => .inr .copy))))
          (.goto (fun _ => .inr .restore)))
  | .inr .restore =>
      .pop (.inl (.inl (3 : Fin 14))) pop
        (.branch isMark
          (.push (.inr source) (cst .mark)
            (.goto (fun _ => .inr .restore)))
          (.goto (fun _ => .inr .done)))
  | .inr .done => .halt

def runAt (source : Fin 4) (dest : Fin 14) :
    Option (Cfg TopGam EntryLabel Sig) → Option (Cfg TopGam EntryLabel Sig) :=
  fun cf => cf.bind (step (machineAt source dest))

theorem machineAt_zero_one : machineAt 0 1 = entryMachine := by
  funext l
  cases l with
  | inl l => rfl
  | inr c => cases c <;> rfl

theorem runAt_zero_one : runAt 0 1 = entryRun := by
  funext cf
  simp [runAt, entryRun, machineAt_zero_one]

theorem start_step_at (source : Fin 4) (dest : Fin 14)
    (v : Sig) (S : ∀ k, List (TopGam k)) :
    (runAt source dest)^[1]
      (some { l := some (.inr .start), var := v, stk := S }) =
        some { l := some (.inr .copy), var := v, stk :=
          (Function.update S (.inl (.inl dest))
            (.delim :: S (.inl (.inl dest)))) } := by
  simp [runAt, machineAt, step, stepAux, cst]

theorem copy_mark_step_at (source : Fin 4) (dest : Fin 14)
    (v : Sig) (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hdest : dest ≠ 3)
    (hsrc : S (.inr source) = .mark :: tail) :
    (runAt source dest)^[1]
      (some { l := some (.inr .copy), var := v, stk := S }) =
        some { l := some (.inr .copy), var := some Cell.mark, stk :=
          (Function.update
            (Function.update
              (Function.update S (.inr source) tail)
              (.inl (.inl dest)) (.mark :: S (.inl (.inl dest))))
            (.inl (.inl (3 : Fin 14)))
            (.mark :: S (.inl (.inl (3 : Fin 14))))) } := by
  simp [runAt, machineAt, step, stepAux, hsrc, pop, isMark, cst,
    hdest, Ne.symm hdest]

theorem copy_empty_step_at (source : Fin 4) (dest : Fin 14)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr source) = []) :
    (runAt source dest)^[1]
      (some { l := some (.inr .copy), var := v, stk := S }) =
        some { l := some (.inr .restore), var := none, stk := S } := by
  simp [runAt, machineAt, step, stepAux, hsrc, pop, isMark]

theorem restore_mark_step_at (source : Fin 4) (dest : Fin 14)
    (v : Sig) (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = .mark :: tail) :
    (runAt source dest)^[1]
      (some { l := some (.inr .restore), var := v, stk := S }) =
        some { l := some (.inr .restore), var := some Cell.mark, stk :=
          (Function.update
            (Function.update S (.inl (.inl (3 : Fin 14))) tail)
            (.inr source) (.mark :: S (.inr source))) } := by
  simp [runAt, machineAt, step, stepAux, hscratch, pop, isMark, cst]

theorem restore_empty_step_at (source : Fin 4) (dest : Fin 14)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    (runAt source dest)^[1]
      (some { l := some (.inr .restore), var := v, stk := S }) =
        some { l := some (.inr .done), var := none, stk := S } := by
  simp [runAt, machineAt, step, stepAux, hscratch, pop, isMark]

end ShiTMPieceEntry
