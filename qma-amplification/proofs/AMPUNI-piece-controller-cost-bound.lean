import «AMPUNI-piece-controller-cost-run»

set_option autoImplicit false

namespace ShiTMPieceController

open ShiTMPieceSchedule

private theorem commandCost_le (n wit anc : Nat) (command : Command) :
    commandCost n wit anc command ≤ 2 * (n + wit + anc + 1) + 4 := by
  cases command with
  | delimiter table => simp [commandCost]
  | add table atom =>
      cases atom <;> simp [commandCost, value] <;> omega

theorem scheduleCost_le (n wit anc : Nat) (xs : List Command) :
    scheduleCost n wit anc xs ≤
      xs.length * (2 * (n + wit + anc + 1) + 4) := by
  induction xs with
  | nil => simp [scheduleCost]
  | cons command xs ih =>
      have hc := commandCost_le n wit anc command
      change commandCost n wit anc command + scheduleCost n wit anc xs ≤
        (xs.length + 1) * (2 * (n + wit + anc + 1) + 4)
      calc
        commandCost n wit anc command + scheduleCost n wit anc xs ≤
            (2 * (n + wit + anc + 1) + 4) +
              xs.length * (2 * (n + wit + anc + 1) + 4) :=
          Nat.add_le_add hc ih
        _ = (xs.length + 1) * (2 * (n + wit + anc + 1) + 4) := by
          simp [Nat.add_mul, Nat.add_comm]

/-- The fixed copy program has a uniform linear step bound in the unary
input, witness, and ancilla header lengths. -/
theorem programCost_le (copy : Fin 3) (n wit anc : Nat) :
    scheduleCost n wit anc (program copy) ≤
      64 * (2 * (n + wit + anc + 1) + 4) := by
  calc
    scheduleCost n wit anc (program copy) ≤
        (program copy).length * (2 * (n + wit + anc + 1) + 4) :=
      scheduleCost_le n wit anc (program copy)
    _ ≤ 64 * (2 * (n + wit + anc + 1) + 4) :=
      Nat.mul_le_mul_right _ (program_length_le_64 copy)

end ShiTMPieceController
