import «AMPUNI-layout-machine»

set_option autoImplicit false
set_option maxRecDepth 10000
namespace ShiTMReadout
open ShiTMLayoutMachine

/-- A bounded constructor tag/layer header, or one of four supplied wire indices. -/
abbrev Command := Fin 5 ⊕ Fin 4
inductive Gate where
  | h (r : Fin 4) | t (r : Fin 4) | cnot (p q : Fin 4)

def gateCommands : Gate → List Command
  | .h r => [.inl 1, .inl 0, .inr r]
  | .t r => [.inl 1, .inl 2, .inr r]
  | .cnot p q => [.inl 1, .inl 4, .inr p, .inr q]

/-- The explicit 37-gate Toffoli template, with symbolic wire registers. -/
def toff (p q r : Fin 4) : List Gate :=
  [.h r, .t p, .t q, .t r, .cnot p q, .t q, .t q,
   .t q, .t q, .t q, .t q, .t q, .cnot p q,
   .cnot q r, .t r, .t r, .t r, .t r, .t r, .t r,
   .t r, .cnot q r, .cnot p r, .t r, .t r, .t r,
   .t r, .t r, .t r, .t r, .cnot p r, .cnot p r,
   .cnot q r, .t r, .cnot q r, .cnot p r, .h r]

def gates : List Gate := toff 0 1 3 ++ toff 1 2 3 ++ toff 0 2 3
def program : List Command := gates.flatMap gateCommands

theorem gates_length : gates.length = 111 := by rfl
theorem program_length : program.length = 363 := by rfl

def unary (n : Nat) : List Cell := List.replicate n .mark ++ [.delim]
def bytes (values : Fin 4 → Nat) : Command → List Cell
  | .inl k => unary k.val
  | .inr k => unary (values k)
def programBytes (values : Fin 4 → Nat) : List Cell := (program.map (bytes values)).flatten

def commandCost (values : Fin 4 → Nat) : Command → Nat
  | .inl _ => 1
  | .inr k => 2*values k+4

def scheduleCost (values : Fin 4 → Nat) (xs : List Command) : Nat :=
  (xs.map (commandCost values)).sum

end ShiTMReadout
