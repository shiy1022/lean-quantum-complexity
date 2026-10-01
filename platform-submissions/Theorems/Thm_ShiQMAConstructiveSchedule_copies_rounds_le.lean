import Definitions.Def_ShiQMAConstructiveSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem ShiQMAConstructiveSchedule.copies_rounds_le (p : Polynomial ℕ) (n : ℕ) :
    3 ^ rounds p n ≤
      3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree) := by sorry
