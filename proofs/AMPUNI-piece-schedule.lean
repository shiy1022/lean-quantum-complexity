import «AMPUNI-copy-local-blocks»

set_option autoImplicit false

namespace ShiTMPieceSchedule

inductive Atom where
  | input | witness | ancilla | one
deriving DecidableEq, Repr

instance : Fintype Atom :=
  Fintype.ofList [.input, .witness, .ancilla, .one]
    (by intro x; cases x <;> simp)

def value (n wit anc : Nat) : Atom → Nat
  | .input => n
  | .witness => wit
  | .ancilla => anc
  | .one => 1

def evalSum (n wit anc : Nat) (atoms : List Atom) : Nat :=
  (atoms.map (value n wit anc)).sum

def evalPiece (n wit anc : Nat) (p : List Atom × List Atom) : Nat × Nat :=
  (evalSum n wit anc p.1, evalSum n wit anc p.2)

/-- Each pair lists the unary sources used for its width and its output base.
The order is fixed, so an initializer may walk this finite schedule in reverse. -/
def copySchedule0 : List (List Atom × List Atom) :=
  [([.input], []),
   ([.witness], [.input]),
   ([.ancilla], [.input, .witness, .witness, .witness]),
   ([.one], [.input, .witness, .witness, .witness, .ancilla])]

def copySchedule1 : List (List Atom × List Atom) :=
  [([.input], [.input, .witness, .witness, .witness, .ancilla, .one]),
   ([.witness], [.input, .witness]),
   ([.ancilla], [.input, .input, .witness, .witness, .witness, .ancilla, .one]),
   ([.one], [.input, .input, .witness, .witness, .witness,
     .ancilla, .ancilla, .one])]

def copySchedule2 : List (List Atom × List Atom) :=
  [([.input], [.input, .input, .witness, .witness, .witness,
     .ancilla, .ancilla, .one, .one]),
   ([.witness], [.input, .witness, .witness]),
   ([.ancilla], [.input, .input, .input, .witness, .witness, .witness,
     .ancilla, .ancilla, .one, .one]),
   ([.one], [.input, .input, .input, .witness, .witness, .witness,
     .ancilla, .ancilla, .ancilla, .one, .one])]

theorem eval_copySchedule0 (n wit anc : Nat) :
    copySchedule0.map (evalPiece n wit anc) =
      ShiTMLayoutMachine.copyPieces0 n wit anc := by
  simp [copySchedule0, evalPiece, evalSum, value,
    ShiTMLayoutMachine.copyPieces0] <;> omega

theorem eval_copySchedule1 (n wit anc : Nat) :
    copySchedule1.map (evalPiece n wit anc) =
      ShiTMLayoutMachine.copyPieces1 n wit anc := by
  simp [copySchedule1, evalPiece, evalSum, value,
    ShiTMLayoutMachine.copyPieces1] <;> omega

theorem eval_copySchedule2 (n wit anc : Nat) :
    copySchedule2.map (evalPiece n wit anc) =
      ShiTMLayoutMachine.copyPieces2 n wit anc := by
  simp [copySchedule2, evalPiece, evalSum, value,
    ShiTMLayoutMachine.copyPieces2] <;> omega

end ShiTMPieceSchedule
