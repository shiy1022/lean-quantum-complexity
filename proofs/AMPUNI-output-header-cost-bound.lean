import «AMPUNI-output-header-schedule»

set_option autoImplicit false

namespace ShiTMOutputHeader

def commandCost (n wit anc : Nat) : Command → Nat
  | .delimiter => 1
  | .add .one => 1
  | .add atom => 2 * value n wit anc atom + 4

def scheduleCost (n wit anc : Nat) : List Command → Nat
  | [] => 0
  | c :: cs => commandCost n wit anc c + scheduleCost n wit anc cs

theorem program_length : program.length = 26 := by decide

private theorem commandCost_le (n wit anc : Nat) (c : Command) :
    commandCost n wit anc c ≤ 2 * (n + wit + anc + 1) + 4 := by
  cases c with
  | delimiter => simp [commandCost]
  | add atom =>
      cases atom <;> simp [commandCost, value] <;> omega

theorem scheduleCost_le (n wit anc : Nat) (xs : List Command) :
    scheduleCost n wit anc xs ≤
      xs.length * (2 * (n + wit + anc + 1) + 4) := by
  induction xs with
  | nil => simp [scheduleCost]
  | cons c xs ih =>
      have hc := commandCost_le n wit anc c
      change commandCost n wit anc c + scheduleCost n wit anc xs ≤
        (xs.length + 1) * (2 * (n + wit + anc + 1) + 4)
      calc
        commandCost n wit anc c + scheduleCost n wit anc xs ≤
            (2 * (n + wit + anc + 1) + 4) +
              xs.length * (2 * (n + wit + anc + 1) + 4) :=
          Nat.add_le_add hc ih
        _ = (xs.length + 1) * (2 * (n + wit + anc + 1) + 4) := by
          simp [Nat.add_mul, Nat.add_comm]

theorem programCost_le (n wit anc : Nat) :
    scheduleCost n wit anc program ≤
      26 * (2 * (n + wit + anc + 1) + 4) := by
  simpa [program_length] using scheduleCost_le n wit anc program

end ShiTMOutputHeader
