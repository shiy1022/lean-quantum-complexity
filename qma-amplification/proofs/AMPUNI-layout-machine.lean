import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTMLayoutMachine

inductive Cell
  | mark | delim | mirrorEnd | tag0 | tag1 | tag2 | tag3 | tag4
  | continueSingle | continueCnotMid | continueCnotEnd
deriving DecidableEq

instance : Fintype Cell :=
  Fintype.ofList
    [.mark, .delim, .mirrorEnd, .tag0, .tag1, .tag2, .tag3, .tag4,
      .continueSingle, .continueCnotMid, .continueCnotEnd]
    (by intro x; cases x <;> simp)

instance : Inhabited Cell := ⟨.mark⟩

abbrev Gam : Fin 14 → Type := fun _ => Cell
abbrev Sig := Option Cell

/-- The accepted layout block occupies the first eleven stacks; stacks 11 and 12 remain
available to the enclosing instruction and circuit parsers. -/
def layoutStack (i : Fin 11) : Fin 14 := ⟨i.val, Nat.lt_trans i.isLt (by omega)⟩

theorem layoutStack_injective : Function.Injective layoutStack := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 14 => x.val) h

def pop : Sig → Option Cell → Sig := fun _ o => o
def get : Sig → Cell := fun s => s.getD .mark
def cst (c : Cell) : Sig → Cell := fun _ => c
def isSome : Sig → Bool := fun s => s.isSome
def isMark : Sig → Bool := fun s => decide (s = some .mark)
def notMirrorEnd : Sig → Bool := fun s => decide (s ≠ some .mirrorEnd)
def bit : Bool → Cell := fun b => if b then .mark else .delim

inductive BaseLabel
  | parseTag | count0 | count1 | count2 | count3 | count4 | instructionDispatch
  | read0 | read1 | read2 | read3 | readCnotFirst | readCnotSecond
  | finish0 | finish1 | finish2 | finish3 | finishCnotMid | finishCnotEnd
  | stripCnotZero | clearScratch | restoreCnotFirst | reverseOutput | instructionDone
  | wire | afterPiece | afterBase | finishPiece | finishBase
  | dispatch
  | emitDelim0 | emitDelim1 | emitDelim2 | emitDelim3 | emitDelim4
  | emitIndex0 | emitIndex1 | emitIndex2 | emitIndex3 | emitIndex4
  | reloadPiece | reloadPieceMirror | reloadPieceSentinel | reloadPieceRestore
  | reloadBase | reloadBaseMirror | reloadBaseSentinel | reloadBaseRestore
  | done | halt
deriving DecidableEq

instance : Fintype BaseLabel :=
  Fintype.ofList
    [.wire, .afterPiece, .afterBase, .finishPiece, .finishBase,
      .parseTag, .count0, .count1, .count2, .count3, .count4, .instructionDispatch,
      .read0, .read1, .read2, .read3, .readCnotFirst, .readCnotSecond,
      .finish0, .finish1, .finish2, .finish3, .finishCnotMid, .finishCnotEnd,
      .stripCnotZero, .clearScratch, .restoreCnotFirst, .reverseOutput, .instructionDone,
      .dispatch,
      .emitDelim0, .emitDelim1, .emitDelim2, .emitDelim3, .emitDelim4,
      .emitIndex0, .emitIndex1, .emitIndex2, .emitIndex3, .emitIndex4,
      .reloadPiece, .reloadPieceMirror, .reloadPieceSentinel, .reloadPieceRestore,
      .reloadBase, .reloadBaseMirror, .reloadBaseSentinel, .reloadBaseRestore,
      .done, .halt]
    (by intro x; cases x <;> simp)

open Turing Turing.TM2

/-- The finite mark-loop windows for all five source instruction tags live in one label type. -/
abbrev MarkLabel := Sigma fun t : Fin 5 => Fin t.val
abbrev Label := BaseLabel ⊕ MarkLabel

instance : Inhabited Label := ⟨Sum.inl .halt⟩

def b (l : BaseLabel) : Label := Sum.inl l

/-- Below `t`, use the corresponding finite mark label; at and above `t`, join directly to
the piece-list reload pass. -/
def markLabel (t : Fin 5) (q : ℕ) : Label :=
  if h : q < t.val then Sum.inr ⟨t, q, h⟩ else b .reloadPiece

def tagCell (t : Fin 5) : Cell :=
  if t.val = 0 then .tag0 else if t.val = 1 then .tag1 else if t.val = 2 then .tag2
  else if t.val = 3 then .tag3 else .tag4

def emitDelimLabel (t : Fin 5) : Label :=
  if t.val = 0 then b .emitDelim0 else if t.val = 1 then b .emitDelim1
  else if t.val = 2 then b .emitDelim2 else if t.val = 3 then b .emitDelim3 else b .emitDelim4

def emitIndexLabel (t : Fin 5) : Label :=
  if t.val = 0 then b .emitIndex0 else if t.val = 1 then b .emitIndex1
  else if t.val = 2 then b .emitIndex2 else if t.val = 3 then b .emitIndex3 else b .emitIndex4

def countLabel (q : Nat) : Label :=
  if q = 0 then b .count0 else if q = 1 then b .count1 else if q = 2 then b .count2
  else if q = 3 then b .count3 else if q = 4 then b .count4 else b .halt

def instructionArmLabel : Sig → Label
  | some .tag0 => b .read0
  | some .tag1 => b .read1
  | some .tag2 => b .read2
  | some .tag3 => b .read3
  | some .tag4 => b .readCnotFirst
  | _ => b .halt

def continuationLabel : Sig → Label
  | some .continueCnotMid => b .stripCnotZero
  | some .continueSingle => b .reverseOutput
  | some .continueCnotEnd => b .reverseOutput
  | _ => b .halt

def finishOperand (t : Fin 5) (continuation : Cell) : Stmt Gam Label Sig :=
  Stmt.push 7 (cst continuation)
    (Stmt.push 7 (fun _ => tagCell t) (Stmt.goto (fun _ => b .wire)))

def operandLoopLabel (t : Fin 5) : Label :=
  if t.val = 0 then b .read0 else if t.val = 1 then b .read1
  else if t.val = 2 then b .read2 else b .read3

def operandFinishLabel (t : Fin 5) : Label :=
  if t.val = 0 then b .finish0 else if t.val = 1 then b .finish1
  else if t.val = 2 then b .finish2 else b .finish3

def readOperand (t : Fin 5) : Stmt Gam Label Sig :=
  Stmt.pop 11 pop (Stmt.branch isMark
    (Stmt.push 0 (cst .mark) (Stmt.goto (fun _ => operandLoopLabel t)))
    (Stmt.goto (fun _ => operandFinishLabel t)))

def dispatchLabel : Sig → Label :=
  fun s => if s = some .tag0 then b .emitDelim0
    else if s = some .tag1 then b .emitDelim1
    else if s = some .tag2 then b .emitDelim2
    else if s = some .tag3 then b .emitDelim3
    else if s = some .tag4 then b .emitDelim4 else b .halt

def emitterIndexStmt (t : Fin 5) : Stmt Gam Label Sig :=
  Stmt.pop 4 pop (Stmt.branch isMark
    (Stmt.push 6 get (Stmt.goto (fun _ => emitIndexLabel t)))
    (Stmt.push 4 (cst .delim)
      (Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => markLabel t 0)))))

/-- A concrete finite machine hosting WIRE-2, EMITX-1 and both NORM-1 reload passes for an
arbitrary unary tag `t`. -/
def machine : Label → Stmt Gam Label Sig
  | .inl .parseTag => Stmt.pop 11 pop (Stmt.branch isMark
      (Stmt.push 12 (cst .mark) (Stmt.goto (fun _ => b .parseTag)))
      (Stmt.goto (fun _ => b .count0)))
  | .inl .count0 => Stmt.pop 12 pop (Stmt.branch isSome
      (Stmt.goto (fun _ => b .count1))
      (Stmt.push 7 (fun _ => tagCell 0) (Stmt.goto (fun _ => b .instructionDispatch))))
  | .inl .count1 => Stmt.pop 12 pop (Stmt.branch isSome
      (Stmt.goto (fun _ => b .count2))
      (Stmt.push 7 (fun _ => tagCell 1) (Stmt.goto (fun _ => b .instructionDispatch))))
  | .inl .count2 => Stmt.pop 12 pop (Stmt.branch isSome
      (Stmt.goto (fun _ => b .count3))
      (Stmt.push 7 (fun _ => tagCell 2) (Stmt.goto (fun _ => b .instructionDispatch))))
  | .inl .count3 => Stmt.pop 12 pop (Stmt.branch isSome
      (Stmt.goto (fun _ => b .count4))
      (Stmt.push 7 (fun _ => tagCell 3) (Stmt.goto (fun _ => b .instructionDispatch))))
  | .inl .count4 => Stmt.pop 12 pop (Stmt.branch isSome
      (Stmt.goto (fun _ => b .halt))
      (Stmt.push 7 (fun _ => tagCell 4) (Stmt.goto (fun _ => b .instructionDispatch))))
  | .inl .instructionDispatch => Stmt.pop 7 pop (Stmt.goto instructionArmLabel)
  | .inl .read0 => readOperand 0
  | .inl .read1 => readOperand 1
  | .inl .read2 => readOperand 2
  | .inl .read3 => readOperand 3
  | .inl .readCnotFirst => Stmt.pop 11 pop (Stmt.branch isMark
      (Stmt.push 12 (cst .mark) (Stmt.goto (fun _ => b .readCnotFirst)))
      (Stmt.goto (fun _ => b .readCnotSecond)))
  | .inl .readCnotSecond => Stmt.pop 11 pop (Stmt.branch isMark
      (Stmt.push 0 (cst .mark) (Stmt.goto (fun _ => b .readCnotSecond)))
      (Stmt.goto (fun _ => b .finishCnotMid)))
  | .inl .finish0 => finishOperand 0 .continueSingle
  | .inl .finish1 => finishOperand 1 .continueSingle
  | .inl .finish2 => finishOperand 2 .continueSingle
  | .inl .finish3 => finishOperand 3 .continueSingle
  | .inl .finishCnotMid => finishOperand 0 .continueCnotMid
  | .inl .finishCnotEnd => finishOperand 4 .continueCnotEnd
  | .inl .done => Stmt.pop 7 pop (Stmt.goto continuationLabel)
  | .inl .stripCnotZero => Stmt.pop 6 pop (Stmt.goto (fun _ => b .clearScratch))
  | .inl .clearScratch => Stmt.pop 3 pop (Stmt.branch isSome
      (Stmt.push 5 get (Stmt.goto (fun _ => b .clearScratch)))
      (Stmt.goto (fun _ => b .restoreCnotFirst)))
  | .inl .restoreCnotFirst => Stmt.pop 12 pop (Stmt.branch isSome
      (Stmt.push 0 (cst .mark) (Stmt.goto (fun _ => b .restoreCnotFirst)))
      (Stmt.goto (fun _ => b .finishCnotEnd)))
  | .inl .reverseOutput => Stmt.pop 6 pop (Stmt.branch isSome
      (Stmt.push 13 get (Stmt.goto (fun _ => b .reverseOutput)))
      (Stmt.goto (fun _ => b .instructionDone)))
  | .inl .wire => Stmt.pop 1 pop (Stmt.branch isMark
      (Stmt.pop 0 pop (Stmt.branch isSome
        (Stmt.push 3 (cst .mark) (Stmt.goto (fun _ => b .wire)))
        (Stmt.goto (fun _ => b .finishPiece))))
      (Stmt.goto (fun _ => b .afterPiece)))
  | .inl .afterPiece => Stmt.pop 3 pop (Stmt.branch isSome
      (Stmt.push 5 get (Stmt.goto (fun _ => b .afterPiece)))
      (Stmt.goto (fun _ => b .afterBase)))
  | .inl .afterBase => Stmt.pop 2 pop (Stmt.branch isMark
      (Stmt.push 5 get (Stmt.goto (fun _ => b .afterBase)))
      (Stmt.goto (fun _ => b .wire)))
  | .inl .finishPiece => Stmt.pop 2 pop (Stmt.branch isMark
      (Stmt.push 4 get (Stmt.goto (fun _ => b .finishPiece)))
      (Stmt.goto (fun _ => b .finishBase)))
  | .inl .finishBase => Stmt.pop 3 pop (Stmt.branch isSome
      (Stmt.push 4 get (Stmt.goto (fun _ => b .finishBase)))
      (Stmt.goto (fun _ => b .dispatch)))
  | .inl .dispatch => Stmt.pop 7 pop (Stmt.goto dispatchLabel)
  | .inl .emitDelim0 => Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => b .emitIndex0))
  | .inl .emitDelim1 => Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => b .emitIndex1))
  | .inl .emitDelim2 => Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => b .emitIndex2))
  | .inl .emitDelim3 => Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => b .emitIndex3))
  | .inl .emitDelim4 => Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => b .emitIndex4))
  | .inl .emitIndex0 => emitterIndexStmt ⟨0, by omega⟩
  | .inl .emitIndex1 => emitterIndexStmt ⟨1, by omega⟩
  | .inl .emitIndex2 => emitterIndexStmt ⟨2, by omega⟩
  | .inl .emitIndex3 => emitterIndexStmt ⟨3, by omega⟩
  | .inl .emitIndex4 => emitterIndexStmt ⟨4, by omega⟩
  | .inl .reloadPiece => Stmt.pop 1 pop (Stmt.branch isSome
      (Stmt.push 5 get (Stmt.goto (fun _ => b .reloadPiece)))
      (Stmt.goto (fun _ => b .reloadPieceMirror)))
  | .inl .reloadPieceMirror => Stmt.pop 8 pop (Stmt.branch notMirrorEnd
      (Stmt.push 1 get (Stmt.push 10 get (Stmt.goto (fun _ => b .reloadPieceMirror))))
      (Stmt.goto (fun _ => b .reloadPieceSentinel)))
  | .inl .reloadPieceSentinel =>
      Stmt.push 8 (cst .mirrorEnd) (Stmt.goto (fun _ => b .reloadPieceRestore))
  | .inl .reloadPieceRestore => Stmt.pop 10 pop (Stmt.branch isSome
      (Stmt.push 8 get (Stmt.goto (fun _ => b .reloadPieceRestore)))
      (Stmt.goto (fun _ => b .reloadBase)))
  | .inl .reloadBase => Stmt.pop 2 pop (Stmt.branch isSome
      (Stmt.push 5 get (Stmt.goto (fun _ => b .reloadBase)))
      (Stmt.goto (fun _ => b .reloadBaseMirror)))
  | .inl .reloadBaseMirror => Stmt.pop 9 pop (Stmt.branch notMirrorEnd
      (Stmt.push 2 get (Stmt.push 10 get (Stmt.goto (fun _ => b .reloadBaseMirror))))
      (Stmt.goto (fun _ => b .reloadBaseSentinel)))
  | .inl .reloadBaseSentinel =>
      Stmt.push 9 (cst .mirrorEnd) (Stmt.goto (fun _ => b .reloadBaseRestore))
  | .inl .reloadBaseRestore => Stmt.pop 10 pop (Stmt.branch isSome
      (Stmt.push 9 get (Stmt.goto (fun _ => b .reloadBaseRestore)))
      (Stmt.goto (fun _ => b .done)))
  | .inr q =>
      Stmt.push 6 (cst .mark) (Stmt.goto (fun _ => markLabel q.1 (q.2.val + 1)))
  | _ => Stmt.halt

theorem markLabel_of_lt (t : Fin 5) (q : ℕ) (hq : q < t.val) :
    markLabel t q = Sum.inr ⟨t, q, hq⟩ := by
  simp [markLabel, hq]

theorem markLabel_end (t : Fin 5) : markLabel t t.val = b .reloadPiece := by
  simp [markLabel]

theorem machine_mark (t : Fin 5) (q : ℕ) (hq : q < t.val) :
    machine (markLabel t q) =
      Stmt.push 6 (cst .mark) (Stmt.goto (fun _ => markLabel t (q + 1))) := by
  rw [markLabel_of_lt t q hq]
  rfl

theorem machine_emitDelim (t : Fin 5) :
    machine (emitDelimLabel t) =
      Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => emitIndexLabel t)) := by
  fin_cases t <;> rfl

theorem machine_emitIndex (t : Fin 5) :
    machine (emitIndexLabel t) = emitterIndexStmt t := by
  fin_cases t <;> rfl

theorem dispatch_tag (t : Fin 5) : dispatchLabel (some (tagCell t)) = emitDelimLabel t := by
  fin_cases t <;> rfl

theorem machine_count (q : Nat) (hq : q < 5) :
    machine (countLabel q) = Stmt.pop 12 pop (Stmt.branch isSome
      (Stmt.goto (fun _ => countLabel (q + 1)))
      (Stmt.push 7 (fun _ => tagCell ⟨q, hq⟩)
        (Stmt.goto (fun _ => b .instructionDispatch)))) := by
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem machine_readOperand (t : Fin 5) (ht : t.val < 4) :
    machine (operandLoopLabel t) = Stmt.pop 11 pop (Stmt.branch isMark
      (Stmt.push 0 (cst .mark) (Stmt.goto (fun _ => operandLoopLabel t)))
      (Stmt.goto (fun _ => operandFinishLabel t))) := by
  have hcases : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 := by omega
  rcases t with ⟨q, hq⟩
  rcases hcases with h | h | h | h <;> simp only [Fin.val_mk] at h <;> subst q <;> rfl

theorem machine_operandFinish (t : Fin 5) (ht : t.val < 4) :
    machine (operandFinishLabel t) = finishOperand t .continueSingle := by
  have hcases : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 := by omega
  rcases t with ⟨q, hq⟩
  rcases hcases with h | h | h | h <;> simp only [Fin.val_mk] at h <;> subst q <;> rfl

/-- The complete finite-label pinning package needed by the accepted layout composite. -/
theorem program_equations (t : Fin 5) :
    machine (b .wire) = Stmt.pop 1 pop (Stmt.branch isMark
      (Stmt.pop 0 pop (Stmt.branch isSome
        (Stmt.push 3 (cst .mark) (Stmt.goto (fun _ => b .wire)))
        (Stmt.goto (fun _ => b .finishPiece))))
      (Stmt.goto (fun _ => b .afterPiece)))
    ∧ machine (b .afterPiece) = Stmt.pop 3 pop (Stmt.branch isSome
      (Stmt.push 5 get (Stmt.goto (fun _ => b .afterPiece)))
      (Stmt.goto (fun _ => b .afterBase)))
    ∧ machine (b .afterBase) = Stmt.pop 2 pop (Stmt.branch isMark
      (Stmt.push 5 get (Stmt.goto (fun _ => b .afterBase)))
      (Stmt.goto (fun _ => b .wire)))
    ∧ machine (b .finishPiece) = Stmt.pop 2 pop (Stmt.branch isMark
      (Stmt.push 4 get (Stmt.goto (fun _ => b .finishPiece)))
      (Stmt.goto (fun _ => b .finishBase)))
    ∧ machine (b .finishBase) = Stmt.pop 3 pop (Stmt.branch isSome
      (Stmt.push 4 get (Stmt.goto (fun _ => b .finishBase)))
      (Stmt.goto (fun _ => b .dispatch)))
    ∧ machine (b .dispatch) = Stmt.pop 7 pop (Stmt.goto dispatchLabel)
    ∧ machine (emitDelimLabel t) = Stmt.push 6 (cst .delim)
      (Stmt.goto (fun _ => emitIndexLabel t))
    ∧ machine (emitIndexLabel t) = Stmt.pop 4 pop (Stmt.branch isMark
      (Stmt.push 6 get (Stmt.goto (fun _ => emitIndexLabel t)))
      (Stmt.push 4 (cst .delim)
        (Stmt.push 6 (cst .delim) (Stmt.goto (fun _ => markLabel t 0)))))
    ∧ (∀ q, q < t.val → machine (markLabel t q) =
      Stmt.push 6 (cst .mark) (Stmt.goto (fun _ => markLabel t (q + 1))))
    ∧ markLabel t t.val = b .reloadPiece
    ∧ machine (b .reloadPiece) = Stmt.pop 1 pop (Stmt.branch isSome
      (Stmt.push 5 get (Stmt.goto (fun _ => b .reloadPiece)))
      (Stmt.goto (fun _ => b .reloadPieceMirror)))
    ∧ machine (b .reloadPieceMirror) = Stmt.pop 8 pop (Stmt.branch notMirrorEnd
      (Stmt.push 1 get (Stmt.push 10 get (Stmt.goto (fun _ => b .reloadPieceMirror))))
      (Stmt.goto (fun _ => b .reloadPieceSentinel)))
    ∧ machine (b .reloadPieceSentinel) =
      Stmt.push 8 (cst .mirrorEnd) (Stmt.goto (fun _ => b .reloadPieceRestore))
    ∧ machine (b .reloadPieceRestore) = Stmt.pop 10 pop (Stmt.branch isSome
      (Stmt.push 8 get (Stmt.goto (fun _ => b .reloadPieceRestore)))
      (Stmt.goto (fun _ => b .reloadBase)))
    ∧ machine (b .reloadBase) = Stmt.pop 2 pop (Stmt.branch isSome
      (Stmt.push 5 get (Stmt.goto (fun _ => b .reloadBase)))
      (Stmt.goto (fun _ => b .reloadBaseMirror)))
    ∧ machine (b .reloadBaseMirror) = Stmt.pop 9 pop (Stmt.branch notMirrorEnd
      (Stmt.push 2 get (Stmt.push 10 get (Stmt.goto (fun _ => b .reloadBaseMirror))))
      (Stmt.goto (fun _ => b .reloadBaseSentinel)))
    ∧ machine (b .reloadBaseSentinel) =
      Stmt.push 9 (cst .mirrorEnd) (Stmt.goto (fun _ => b .reloadBaseRestore))
    ∧ machine (b .reloadBaseRestore) = Stmt.pop 10 pop (Stmt.branch isSome
      (Stmt.push 9 get (Stmt.goto (fun _ => b .reloadBaseRestore)))
      (Stmt.goto (fun _ => b .done))) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, machine_emitDelim t, ?_, machine_mark t, markLabel_end t,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [emitterIndexStmt] using machine_emitIndex t

end ShiTMLayoutMachine
