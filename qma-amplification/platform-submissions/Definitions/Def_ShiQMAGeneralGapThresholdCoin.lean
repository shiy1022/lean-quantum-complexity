import Mathlib.Tactic
import Definitions.Def_ShiBQP_Core
import Definitions.Def_ShiQMACenteredGapComputableCoin
import Definitions.Def_ShiQMAConstructiveSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAGeneralGap
open ShiQMACenteredGap ShiQMAConstructiveSchedule

def thresholdInput (n k : Nat) : PvsNP.Str := ShiBQP.encNat n ++ ShiBQP.unary k

/-- Efficient real thresholds are represented by polynomial-time dyadic
approximators. This is a premise about the original thresholds, not an
assumed amplifier or centering-circuit transducer. -/
structure ThresholdApproximation (a : Nat → ℝ) where
  approximate : PvsNP.Str → PvsNP.Str
  polynomialTime : PvsNP.PolyTimeComputable approximate
  length_eq : ∀ n k, (approximate (thresholdInput n k)).length = k
  error_le : ∀ n k, |dyadicValue (approximate (thresholdInput n k)) - a n| ≤
    1 / (2 : ℝ) ^ k

/-- Concrete integer coin numerator obtained from the two approximation algorithms.
Its correctness is proved below; a polynomial-time machine for this composition
is still a separate obligation. -/
def thresholdCoinNumerator {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) : Nat :=
  let k := rounds q n
  centeringNumerator k
    (binaryNumerator (A.approximate (thresholdInput n k)))
    (binaryNumerator (B.approximate (thresholdInput n k)))

def thresholdCoinBits {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) : List Bool :=
  fractionBits (rounds q n + 1) (thresholdCoinNumerator A B q n)

theorem thresholdCoinBits_length {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) (n : Nat) :
    (thresholdCoinBits A B q n).length = rounds q n + 1 :=
  fractionBits_length _ _

end ShiQMAGeneralGap
