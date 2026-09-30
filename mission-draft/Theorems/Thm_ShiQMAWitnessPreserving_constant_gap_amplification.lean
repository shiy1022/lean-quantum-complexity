import Definitions.Def_ShiQMAWitnessPreservingInterface

set_option autoImplicit false

namespace ShiQMAWitnessPreserving
open ShiShallow ShiClassQMA ShiClassQMAU

/-- The constant-threshold case of Marriott–Watrous amplification, keeping
exactly the original witness qubit count. -/
theorem constant_gap_amplification
    (F : QMAFamily) (L : Language Bool)
    (hu : UniformQMA F) (hw : ShiBQP.WellFormed F.toFamily)
    (hp : ShiBQP.PolyBounded F.toFamily) (p : Polynomial ℕ)
    (hv : VerifiesWith F L (fun _ => (2 : ℝ) / 3) (fun _ => (1 : ℝ) / 3)) :
    ∃ G : QMAFamily,
      (∀ n, G.wit n = F.wit n) ∧
      UniformQMA G ∧ ShiBQP.WellFormed G.toFamily ∧
      ShiBQP.PolyBounded G.toFamily ∧
      VerifiesWith G L
        (fun n => 1 - ((1 : ℝ) / 2) ^ (p.eval n))
        (fun n => ((1 : ℝ) / 2) ^ (p.eval n)) := by
  sorry

end ShiQMAWitnessPreserving
