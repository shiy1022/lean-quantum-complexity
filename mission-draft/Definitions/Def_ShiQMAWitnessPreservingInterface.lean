import Definitions.Def_ShiClassQMAU

set_option autoImplicit false

namespace ShiQMAWitnessPreserving
open ShiShallow ShiClassQMA ShiClassQMAU

/-- Completeness and soundness at length-dependent thresholds, with soundness
quantified over every normalized witness. -/
def VerifiesWith (F : QMAFamily) (L : Language Bool)
    (c s : Nat → ℝ) : Prop :=
  ∀ w : PvsNP.Str,
    (w ∈ L → ∃ ψ : QState (F.wit w.length), Normalized ψ ∧
      c w.length ≤ F.acceptWith (ShiBQP.toBits w) ψ) ∧
    (w ∉ L → ∀ ψ : QState (F.wit w.length), Normalized ψ →
      F.acceptWith (ShiBQP.toBits w) ψ ≤ s w.length)

/-- Natural number represented by a list of binary digits. -/
def binaryNumerator : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + binaryNumerator bs

/-- Dyadic rational represented by binary fractional digits. -/
noncomputable def dyadicValue (bs : List Bool) : ℝ :=
  (binaryNumerator bs : ℝ) / (2 : ℝ) ^ bs.length

def thresholdInput (n k : Nat) : PvsNP.Str :=
  ShiBQP.encNat n ++ ShiBQP.unary k

/-- An efficiently approximable threshold, as in the checked copy-based
development. -/
structure ThresholdApproximation (a : Nat → ℝ) where
  approximate : PvsNP.Str → PvsNP.Str
  polynomialTime : PvsNP.PolyTimeComputable approximate
  length_eq : ∀ n k, (approximate (thresholdInput n k)).length = k
  error_le : ∀ n k, |dyadicValue (approximate (thresholdInput n k)) - a n| ≤
    1 / (2 : ℝ) ^ k

end ShiQMAWitnessPreserving
