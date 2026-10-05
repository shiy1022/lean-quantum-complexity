import «AMPUNI-constructive-closed-amplification»

set_option autoImplicit false

namespace ShiQMAAmplification
open ShiShallow ShiClassQMA ShiClassQMAU

/-- Copy-based, polynomial-error QMA amplification.

The verifier is uniformly generated, well formed, and polynomially bounded.
Soundness holds for every normalized witness, including witnesses entangled
across the repeated registers. The witness length may grow polynomially.
The proof has no assumed encoding transformer and no `sorryAx` dependency.
-/
theorem polynomial_error_amplification
    (L : Language Bool)
    (hL : L ∈ QMAU ((2 : ℝ) / 3) ((1 : ℝ) / 3))
    (p : Polynomial ℕ) :
    ∃ G : QMAFamily,
      UniformQMA G ∧ ShiBQP.WellFormed G.toFamily ∧
      ShiBQP.PolyBounded G.toFamily ∧
      ∀ w : PvsNP.Str,
        (w ∈ L → ∃ ψ : QState (G.wit w.length),
          Normalized ψ ∧
          1 - ((1 : ℝ) / 2) ^ (p.eval w.length) ≤
            G.acceptWith (ShiBQP.toBits w) ψ) ∧
        (w ∉ L → ∀ ψ : QState (G.wit w.length),
          Normalized ψ → G.acceptWith (ShiBQP.toBits w) ψ ≤
            ((1 : ℝ) / 2) ^ (p.eval w.length)) := by
  exact ShiQMAConstructiveSchedule.qmaU_polynomial_error_amplification_closed L hL p

end ShiQMAAmplification

#print axioms ShiQMAAmplification.polynomial_error_amplification
