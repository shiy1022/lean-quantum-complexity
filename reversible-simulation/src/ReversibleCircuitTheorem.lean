import ReversibleBooleanClean
import ReversibleQuantum

set_option autoImplicit false

namespace ShiReversible

/-- A finite Boolean circuit with `n` input wires, `k` fresh result wires, and `m` outputs. -/
structure SingleAssignmentCircuit (n k m : Nat) where
  nodes : List (Assignment (n + k))
  targets_distinct : (nodes.map Assignment.target).Nodup
  targets_auxiliary : ∀ a ∈ nodes, n ≤ a.target.val
  nodes_length : nodes.length = k
  read : Fin m → Fin (n + k)

def inputMemory {n k : Nat} (x : Bits n) : Bits (n + k) :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else false

theorem inputMemory_input {n k : Nat} (x : Bits n) (i : Fin n) :
    inputMemory (k := k) x (Fin.castAdd k i) = x i := by
  simp [inputMemory]

theorem inputMemory_auxiliary {n k : Nat} (x : Bits n) (i : Fin k) :
    inputMemory x (Fin.natAdd n i) = false := by
  simp [inputMemory]

def SingleAssignmentCircuit.eval {n k m : Nat} (c : SingleAssignmentCircuit n k m)
    (x : Bits n) : Bits m :=
  fun i => evalAssignments c.nodes (inputMemory x) (c.read i)

def SingleAssignmentCircuit.reversible {n k m : Nat} (c : SingleAssignmentCircuit n k m) :
    List (Instruction (n + k) m) := cleanCircuit (compileAssignments c.nodes) c.read

theorem SingleAssignmentCircuit.clean_correct {n k m : Nat}
    (c : SingleAssignmentCircuit n k m) (x : Bits n) (y : Bits m) :
    execute c.reversible (inputMemory x, y) =
      (inputMemory x, fun i => xor (y i) (c.eval x i)) := by
  apply cleanAssignments_correct c.nodes c.targets_distinct c.read
  intro a ha
  simp [inputMemory, Nat.not_lt.mpr (c.targets_auxiliary a ha)]

/-- Closed finite-circuit simulation theorem; uniform TM simulation remains a separate target. -/
theorem SingleAssignmentCircuit.quantum_clean_correct {n k m : Nat}
    (c : SingleAssignmentCircuit n k m) (x : Bits n) :
    quantumRun c.reversible (basis (inputMemory x, fun _ => false)) =
      basis (inputMemory x, c.eval x) := by
  rw [quantumRun_basis, c.clean_correct]
  simp

theorem SingleAssignmentCircuit.size_bound {n k m : Nat}
    (c : SingleAssignmentCircuit n k m) : c.reversible.length ≤ 4 * k + m := by
  simpa [SingleAssignmentCircuit.reversible, c.nodes_length] using
    cleanAssignments_size c.nodes c.read

end ShiReversible
