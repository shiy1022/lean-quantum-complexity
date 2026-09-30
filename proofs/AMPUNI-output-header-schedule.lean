import «AMPUNI-layout-machine»
import Definitions.Def_ShiBQP_Core

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ShiTMOutputHeader

open ShiTMLayoutMachine

inductive Atom where
  | input | witness | ancilla | one
deriving DecidableEq

instance : Fintype Atom :=
  Fintype.ofList [.input, .witness, .ancilla, .one]
    (by intro x; cases x <;> simp)

inductive Command where
  | add (atom : Atom) | delimiter
deriving DecidableEq

instance : Fintype Command :=
  Fintype.ofList
    [.add .input, .add .witness, .add .ancilla, .add .one, .delimiter]
    (by intro x; cases x with
      | add atom => cases atom <;> simp
      | delimiter => simp)

def value (n wit anc : Nat) : Atom → Nat
  | .input => n
  | .witness => wit
  | .ancilla => anc
  | .one => 1

def cells (n wit anc : Nat) : Command → List Cell
  | .add a => List.replicate (value n wit anc a) .mark
  | .delimiter => [.delim]

def eval (n wit anc : Nat) : List Command → List Cell → List Cell
  | [], acc => acc
  | c :: cs, acc => eval n wit anc cs (cells n wit anc c ++ acc)

def fieldA : List Atom := [.witness, .witness, .witness]
def fieldB : List Atom :=
  [.input, .input, .ancilla, .ancilla, .ancilla, .one, .one, .one]
def fieldC : List Atom :=
  [.input, .input, .input, .witness, .witness, .witness,
    .ancilla, .ancilla, .ancilla, .one, .one, .one]

def fieldProgram (xs : List Atom) : List Command := xs.map .add ++ [.delimiter]
def program : List Command :=
  fieldProgram fieldA ++ fieldProgram fieldB ++ fieldProgram fieldC

private theorem eval_append (n wit anc : Nat) (xs ys : List Command)
    (acc : List Cell) :
    eval n wit anc (xs ++ ys) acc = eval n wit anc ys (eval n wit anc xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons c xs ih =>
      simp only [List.cons_append, eval]
      exact ih (cells n wit anc c ++ acc)

private theorem eval_adds (n wit anc : Nat) (xs : List Atom)
    (acc : List Cell) :
    eval n wit anc (xs.map Command.add) acc =
      List.replicate (xs.map (value n wit anc)).sum Cell.mark ++ acc := by
  induction xs generalizing acc with
  | nil => simp [eval]
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, eval, cells]
      rw [ih]
      rw [← List.append_assoc, ← List.replicate_add]
      rw [Nat.add_comm (xs.map (value n wit anc)).sum
        (value n wit anc a)]

private theorem eval_field (n wit anc : Nat) (xs : List Atom)
    (acc : List Cell) :
    eval n wit anc (fieldProgram xs) acc =
      Cell.delim :: List.replicate (xs.map (value n wit anc)).sum Cell.mark ++ acc := by
  rw [fieldProgram, eval_append, eval_adds]
  rfl

/-- The fixed command program builds the reverse of the three amplified
numeric headers. The circuit parser can prepend its reversed output next. -/
theorem program_correct (n wit anc : Nat) (acc : List Cell) :
    eval n wit anc program acc =
      Cell.delim :: List.replicate
        (3 * n + 3 * wit + 3 * anc + 3) Cell.mark ++
      Cell.delim :: List.replicate (2 * n + 3 * anc + 3) Cell.mark ++
      Cell.delim :: List.replicate (3 * wit) Cell.mark ++ acc := by
  have hA : (fieldA.map (value n wit anc)).sum = 3 * wit := by
    simp [fieldA, value]
    omega
  have hB : (fieldB.map (value n wit anc)).sum = 2 * n + 3 * anc + 3 := by
    simp [fieldB, value]
    omega
  have hC : (fieldC.map (value n wit anc)).sum =
      3 * n + 3 * wit + 3 * anc + 3 := by
    simp [fieldC, value]
    omega
  rw [program, eval_append, eval_append, eval_field, eval_field, eval_field,
    hA, hB, hC]
  simp only [List.append_assoc]

theorem program_correct_encoding (n wit anc : Nat) :
    eval n wit anc program [] =
      ((ShiBQP.encNat (3 * wit) ++
        ShiBQP.encNat (2 * n + 3 * anc + 3) ++
        ShiBQP.encNat (3 * n + 3 * wit + 3 * anc + 3)).map bit).reverse := by
  rw [program_correct]
  simp [ShiBQP.encNat, bit, List.map_append, List.reverse_append,
    List.append_assoc]

end ShiTMOutputHeader
