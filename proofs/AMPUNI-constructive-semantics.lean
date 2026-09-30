import «AMPUNI-constructive-family»
import «AMPUNI-acceptWith-local»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAConstructiveSchedule
open ShiShallow ShiClassQMA ShiQMAVariableRounds ShiQMAErrorIteration

/-- The constructive logarithmic schedule reaches the same pointwise
completeness and soundness targets as the exact `roundsFor (p.eval n)`
schedule. -/
theorem constructiveFamily_verifies (F : QMAFamily)
    (L : Language Bool) (p : Polynomial ℕ)
    (hF : Verifies F L ((2 : ℝ) / 3) ((1 : ℝ) / 3)) :
    ∀ w : PvsNP.Str,
      (w ∈ L →
        ∃ ψ : QState ((constructiveFamily F p).wit w.length),
          Normalized ψ ∧
          1 - ((1 : ℝ) / 2) ^ (p.eval w.length) ≤
            (constructiveFamily F p).acceptWith (ShiBQP.toBits w) ψ) ∧
      (w ∉ L →
        ∀ ψ : QState ((constructiveFamily F p).wit w.length),
          Normalized ψ →
          (constructiveFamily F p).acceptWith (ShiBQP.toBits w) ψ ≤
            ((1 : ℝ) / 2) ^ (p.eval w.length)) := by
  intro w
  have h := iter_verifies F L hF (rounds p w.length) w
  have he := error_rounds p w.length
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hb⟩ := h.1 hw
    refine ⟨ψ, hψ, ?_⟩
    have hv := varying_acceptWith F (rounds p)
      (ShiBQP.toBits w) ψ
    change (varying F (rounds p)).acceptWith
      (ShiBQP.toBits w) ψ ≥
        1 - ((1 : ℝ) / 2) ^ (p.eval w.length)
    rw [hv]
    linarith
  · intro hw ψ hψ
    have hv := varying_acceptWith F (rounds p)
      (ShiBQP.toBits w) ψ
    change (varying F (rounds p)).acceptWith
      (ShiBQP.toBits w) ψ ≤
        ((1 : ℝ) / 2) ^ (p.eval w.length)
    rw [hv]
    exact (h.2 hw ψ hψ).trans he

end ShiQMAConstructiveSchedule
