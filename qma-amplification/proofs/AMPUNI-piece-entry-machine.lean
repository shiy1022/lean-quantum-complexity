import «AMPUNI-retained-finite»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

inductive Control where
  | start | copy | restore | done
deriving DecidableEq

instance : Fintype Control :=
  Fintype.ofList [.start, .copy, .restore, .done]
    (by intro x; cases x <;> simp)

abbrev EntryLabel := TopLabel ⊕ Control

def liftTopStmt : Stmt TopGam TopLabel Sig → Stmt TopGam EntryLabel Sig
  | .push k f q => .push k f (liftTopStmt q)
  | .peek k f q => .peek k f (liftTopStmt q)
  | .pop k f q => .pop k f (liftTopStmt q)
  | .load f q => .load f (liftTopStmt q)
  | .branch f q₁ q₂ => .branch f (liftTopStmt q₁) (liftTopStmt q₂)
  | .goto f => .goto (fun v => .inl (f v))
  | .halt => .halt

/-- One reusable unary-piece constructor: the source is retained header stack 0, the
destination is layout stack 1, and layout stack 3 is temporary scratch. Later scheduling
must invoke it in reverse piece order because stack pushes prepend. -/
def entryMachine : EntryLabel → Stmt TopGam EntryLabel Sig
  | .inl l => liftTopStmt (topMachine l)
  | .inr .start =>
      .push (.inl (.inl (1 : Fin 14))) (cst .delim)
        (.goto (fun _ => .inr .copy))
  | .inr .copy =>
      .pop (.inr (0 : Fin 4)) pop
        (.branch isMark
          (.push (.inl (.inl (1 : Fin 14))) (cst .mark)
            (.push (.inl (.inl (3 : Fin 14))) (cst .mark)
              (.goto (fun _ => .inr .copy))))
          (.goto (fun _ => .inr .restore)))
  | .inr .restore =>
      .pop (.inl (.inl (3 : Fin 14))) pop
        (.branch isMark
          (.push (.inr (0 : Fin 4)) (cst .mark)
            (.goto (fun _ => .inr .restore)))
          (.goto (fun _ => .inr .done)))
  | .inr .done => .halt

def entryRun : Option (Cfg TopGam EntryLabel Sig) →
    Option (Cfg TopGam EntryLabel Sig) :=
  fun cf => cf.bind (step entryMachine)

theorem entry_start_step (v : Sig) (S : ∀ k, List (TopGam k)) :
    entryRun^[1]
      (some { l := some (.inr .start), var := v, stk := S }) =
        some { l := some (.inr .copy), var := v, stk := (Function.update S (.inl (.inl (1 : Fin 14))) (.delim :: S (.inl (.inl (1 : Fin 14))))) } := by
  simp [entryRun, entryMachine, step, stepAux, cst]

theorem entry_copy_mark_step (v : Sig) (S : ∀ k, List (TopGam k))
    (tail : List Cell)
    (hsrc : S (.inr (0 : Fin 4)) = .mark :: tail) :
    entryRun^[1]
      (some { l := some (.inr .copy), var := v, stk := S }) =
        some { l := some (.inr .copy), var := some Cell.mark, stk := (Function.update
            (Function.update
              (Function.update S (.inr (0 : Fin 4)) tail)
              (.inl (.inl (1 : Fin 14)))
              (.mark :: S (.inl (.inl (1 : Fin 14)))))
            (.inl (.inl (3 : Fin 14)))
            (.mark :: S (.inl (.inl (3 : Fin 14))))) } := by
  simp [entryRun, entryMachine, step, stepAux,
    hsrc, pop, isMark, cst]

theorem entry_copy_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr (0 : Fin 4)) = []) :
    entryRun^[1]
      (some { l := some (.inr .copy), var := v, stk := S }) =
        some { l := some (.inr .restore), var := none, stk := S } := by
  simp [entryRun, entryMachine, step, stepAux,
    hsrc, pop, isMark]

theorem entry_restore_mark_step (v : Sig) (S : ∀ k, List (TopGam k))
    (tail : List Cell)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = .mark :: tail) :
    entryRun^[1]
      (some { l := some (.inr .restore), var := v, stk := S }) =
        some { l := some (.inr .restore), var := some Cell.mark, stk := (Function.update
            (Function.update S (.inl (.inl (3 : Fin 14))) tail)
            (.inr (0 : Fin 4))
            (.mark :: S (.inr (0 : Fin 4)))) } := by
  simp [entryRun, entryMachine, step, stepAux,
    hscratch, pop, isMark, cst]

theorem entry_restore_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    entryRun^[1]
      (some { l := some (.inr .restore), var := v, stk := S }) =
        some { l := some (.inr .done), var := none, stk := S } := by
  simp [entryRun, entryMachine, step, stepAux,
    hscratch, pop, isMark]

end ShiTMPieceEntry
