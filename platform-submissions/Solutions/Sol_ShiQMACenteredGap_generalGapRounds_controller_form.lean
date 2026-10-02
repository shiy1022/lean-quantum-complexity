import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n =
      (3 * (Nat.log 2 (q.eval 1 + 1) + 4) + Nat.log 2 (p.eval 1 + 1) + 4) +
      (3 * q.natDegree + p.natDegree) * (Nat.log 2 (n + 1) + 1) := by
  dsimp [generalGapRounds, normalizationRounds, rounds, exponentBudget]
  ring
