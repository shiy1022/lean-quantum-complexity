import «AMPUNI-piece-program-copies»
import «AMPUNI-mark-block-run»

/-!
This file defines the finite TM2 controller for one copy's fixed width/base
piece program. The proof
that its `work` states simulate `mark_block_run_at`, and the bounded full-program
run theorem, remain to be supplied before this is imported by `htrans`.
-/

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry ShiTMPieceSchedule

/-- A program has at most 64 commands. Slot 64 is the terminal dispatch slot. -/
abbrev PC := Fin 65

def nextPC (pc : PC) : PC :=
  ⟨(pc.val + 1) % 65, Nat.mod_lt _ (by decide)⟩

def commandAt : List Command → Nat → Option Command
  | [], _ => none
  | command :: _, 0 => some command
  | _ :: rest, index + 1 => commandAt rest index

def source : Atom → Fin 4
  | .input => 0
  | .witness => 1
  | .ancilla => 2
  | .one => 0  -- `.one` is handled directly, never by the copy loop.

def destination : Table → Fin 14
  | .width => 1
  | .base => 2

/-- The control alphabet is finite: three copies, 65 program counters, ten
commands, and the four states of the already-proved unary-copy machine. -/
inductive Label where
  | top (l : TopLabel)
  | dispatch (copy : Fin 3) (pc : PC)
  | work (copy : Fin 3) (pc : PC) (atom : Atom) (table : Table)
      (phase : Control)
  | finished (copy : Fin 3)
deriving DecidableEq, Fintype

def liftEntryStmt (copy : Fin 3) (pc : PC) (atom : Atom) (table : Table) :
    Stmt TopGam EntryLabel Sig → Stmt TopGam Label Sig
  | .push k f q => .push k f (liftEntryStmt copy pc atom table q)
  | .peek k f q => .peek k f (liftEntryStmt copy pc atom table q)
  | .pop k f q => .pop k f (liftEntryStmt copy pc atom table q)
  | .load f q => .load f (liftEntryStmt copy pc atom table q)
  | .branch f q₁ q₂ =>
      .branch f (liftEntryStmt copy pc atom table q₁)
        (liftEntryStmt copy pc atom table q₂)
  | .goto f => .goto (fun v =>
      match f v with
      | .inl l => .top l
      | .inr phase => .work copy pc atom table phase)
  | .halt => .halt

/-- Dispatching a delimiter or the constant one takes one step. For a retained
unary field, the command enters the proven copy/restore loop at `.copy`, since
the delimiter (if any) was already emitted by its own preceding command. -/
def machine : Label → Stmt TopGam Label Sig
  | .top l => liftEntryStmt 0 0 .input .width (machineAt 0 1 (.inl l))
  | .dispatch copy pc =>
      match commandAt (program copy) pc.val with
      | none => .goto (fun _ => .finished copy)
      | some (.delimiter table) =>
          .push (.inl (.inl (destination table))) (cst .delim)
            (.goto (fun _ => .dispatch copy (nextPC pc)))
      | some (.add table .one) =>
          .push (.inl (.inl (destination table))) (cst .mark)
            (.goto (fun _ => .dispatch copy (nextPC pc)))
      | some (.add table atom) =>
          .goto (fun _ => .work copy pc atom table .copy)
  | .work copy pc _atom _table .done =>
      .goto (fun _ => .dispatch copy (nextPC pc))
  | .work copy pc atom table phase =>
      liftEntryStmt copy pc atom table
        (machineAt (source atom) (destination table) (.inr phase))
  | .finished _ => .halt

def run : Option (Cfg TopGam Label Sig) → Option (Cfg TopGam Label Sig) :=
  fun cf => cf.bind (step machine)

theorem dispatch_delimiter_step (copy : Fin 3) (pc : PC) (table : Table)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hcommand : commandAt (program copy) pc.val = some (.delimiter table)) :
    run^[1] (some { l := some (.dispatch copy pc), var := v, stk := S }) =
      some { l := some (.dispatch copy (nextPC pc)), var := v, stk :=
        (Function.update S (.inl (.inl (destination table)))
          (.delim :: S (.inl (.inl (destination table))))) } := by
  simp [run, machine, hcommand, step, stepAux, cst]

theorem dispatch_one_step (copy : Fin 3) (pc : PC) (table : Table)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hcommand : commandAt (program copy) pc.val = some (.add table .one)) :
    run^[1] (some { l := some (.dispatch copy pc), var := v, stk := S }) =
      some { l := some (.dispatch copy (nextPC pc)), var := v, stk :=
        (Function.update S (.inl (.inl (destination table)))
          (.mark :: S (.inl (.inl (destination table))))) } := by
  simp [run, machine, hcommand, step, stepAux, cst]

theorem dispatch_field_step (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt (program copy) pc.val = some (.add table atom))
    (hone : atom ≠ .one) :
    run^[1] (some { l := some (.dispatch copy pc), var := v, stk := S }) =
      some { l := some (.work copy pc atom table .copy), var := v, stk := S } := by
  cases atom <;> simp_all [run, machine, step, stepAux]

theorem work_done_step (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (.work copy pc atom table .done), var := v, stk := S }) =
      some { l := some (.dispatch copy (nextPC pc)), var := v, stk := S } := by
  simp [run, machine, step, stepAux]

/- Future proof obligations (not axioms or assumptions):
1. Prove `nextPC` does not wrap on a reachable dispatch state, using
   `program_length_le_64`.
2. Lift `mark_block_run_at` through `liftEntryStmt`; add the two dispatcher
   transitions to show one `.add` command takes `2 * value + 4` steps.
3. Induct over the bounded command list. Match the resulting stack update to
   `runCommands`, then use `run_program0/1/2` for exact `copyPieces` contents.
4. Connect the `finished` state to the next copy's parse/reload entry point.
-/

end ShiTMPieceController
