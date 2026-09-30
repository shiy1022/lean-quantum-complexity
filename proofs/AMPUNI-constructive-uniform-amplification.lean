import «AMPUNI-constructive-transducer»
import «AMPUNI-constructive-semantics»
import «INPUT-RETENTION»

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace ShiQMAConstructiveSchedule
open ShiShallow ShiClassQMA ShiClassQMAU

/-- Input-dependent constructive amplification preserves polynomial-time
uniformity, with the concrete encoding transformer supplied. -/
theorem constructiveFamily_uniform (F : QMAFamily) (p : Polynomial ℕ)
    (huniform : UniformQMA F)
    (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily) :
    UniformQMA (constructiveFamily F p) := by
  obtain ⟨g, hg, hmap⟩ :=
    ShiTMConstructiveConcrete.constructive_encoding_transducer F p hwell hpoly
  obtain ⟨f, hf, hout⟩ :=
    ShiTMInputRetention.uniformQMA_has_length_aware_generator F huniform
  refine ⟨g ∘ f, PvsNP.polyTimeComputable_comp f g hf hg, ?_⟩
  intro n
  rw [Function.comp_apply, hout, hmap]

/-- Uniform QMA amplification to every polynomial exponential error target.
The construction uses polynomially many witness copies. All machine
construction and runtime obligations are discharged in the local chain;
its imported reference-theorem dependencies are recorded by the axiom audit. -/
theorem qmaU_polynomial_error_amplification
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
  obtain ⟨F, huniform, hwell, hpoly, hverifies⟩ := hL
  exact ⟨constructiveFamily F p,
    constructiveFamily_uniform F p huniform hwell hpoly,
    constructiveFamily_wellFormed F p hwell,
    constructiveFamily_polyBounded F p hpoly,
    constructiveFamily_verifies F L p hverifies⟩

end ShiQMAConstructiveSchedule

#print axioms ShiQMAConstructiveSchedule.qmaU_polynomial_error_amplification
