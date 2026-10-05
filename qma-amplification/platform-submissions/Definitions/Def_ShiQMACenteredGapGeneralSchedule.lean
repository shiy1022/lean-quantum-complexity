import Mathlib.Tactic
import Definitions.Def_ShiQMACenteredGap
import Definitions.Def_ShiQMAConstructiveSchedule

set_option autoImplicit false

namespace ShiQMACenteredGap
open ShiQMAConstructiveSchedule

def normalizationRounds (q : Polynomial ℕ) (n : Nat) : Nat :=
  3 * rounds q n
def generalGapRounds (q p : Polynomial ℕ) (n : Nat) : Nat :=
  normalizationRounds q n + rounds p n

end ShiQMACenteredGap
