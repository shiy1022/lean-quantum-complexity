import Definitions.Def_ShiQMAWitnessPreservingInterface

set_option autoImplicit false

namespace ShiQMAWitnessPreserving
open ShiShallow ShiClassQMA ShiClassQMAU

/-- The open Marriott–Watrous target: strong QMA error reduction with exactly
the original number of witness qubits at every input length. -/
theorem general_threshold_amplification {a b : Nat → ℝ}
    (F : QMAFamily) (L : Language Bool)
    (hu : UniformQMA F) (hw : ShiBQP.WellFormed F.toFamily)
    (hp : ShiBQP.PolyBounded F.toFamily)
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q p : Polynomial ℕ)
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, a n ≤ 1) (hab : ∀ n, b n ≤ a n)
    (hgap : ∀ n, (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n))
    (hv : VerifiesWith F L a b) :
    ∃ G : QMAFamily,
      (∀ n, G.wit n = F.wit n) ∧
      UniformQMA G ∧ ShiBQP.WellFormed G.toFamily ∧
      ShiBQP.PolyBounded G.toFamily ∧
      VerifiesWith G L
        (fun n => 1 - ((1 : ℝ) / 2) ^ (p.eval n))
        (fun n => ((1 : ℝ) / 2) ^ (p.eval n)) := by
  sorry

end ShiQMAWitnessPreserving
