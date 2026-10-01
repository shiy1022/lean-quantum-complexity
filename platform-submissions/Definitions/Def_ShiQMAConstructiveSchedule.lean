import Mathlib.Tactic
import Definitions.Def_ShiQMAErrorIteration

set_option autoImplicit false

namespace ShiQMAConstructiveSchedule

def exponentBudget (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  Nat.log 2 (p.eval 1 + 1) + 1 +
    p.natDegree * (Nat.log 2 (n + 1) + 1)

def rounds (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  exponentBudget p n + 3

end ShiQMAConstructiveSchedule
