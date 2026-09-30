import «AMPUNI-variable-semantics»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAVariableRounds
open ShiShallow ShiClassQMA ShiQMAErrorIteration

/-- Acceptance at length `n` depends only on that length's selected verifier. -/
theorem varying_acceptWith (F : QMAFamily) (rounds : Nat → Nat)
    {n : Nat} (x : Bits n)
    (ψ : QState ((iter F (rounds n)).wit n)) :
    (varying F rounds).acceptWith x ψ =
      (iter F (rounds n)).acceptWith x ψ := by
  rfl

/-- Transfer the pointwise bounds to the packaged length-dependent family. -/
theorem polynomialFamily_verifies (F : QMAFamily) (L : Language Bool)
    (p : Polynomial ℕ) (hF : Verifies F L ((2 : ℝ) / 3) ((1 : ℝ) / 3)) :
    ∀ w : PvsNP.Str,
      (w ∈ L →
        ∃ ψ : QState ((polynomialFamily F p).wit w.length),
          Normalized ψ ∧
          1 - ((1 : ℝ) / 2) ^ (p.eval w.length) ≤
            (polynomialFamily F p).acceptWith (ShiBQP.toBits w) ψ) ∧
      (w ∉ L →
        ∀ ψ : QState ((polynomialFamily F p).wit w.length),
          Normalized ψ →
          (polynomialFamily F p).acceptWith (ShiBQP.toBits w) ψ ≤
            ((1 : ℝ) / 2) ^ (p.eval w.length)) := by
  intro w
  have h := iter_verifies_variable_threshold F L p hF w
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hb⟩ := h.1 hw
    refine ⟨ψ, hψ, ?_⟩
    have he := varying_acceptWith F (fun n => roundsFor (p.eval n))
      (ShiBQP.toBits w) ψ
    change (varying F (fun n => roundsFor (p.eval n))).acceptWith
      (ShiBQP.toBits w) ψ ≥ 1 - ((1 : ℝ) / 2) ^ (p.eval w.length)
    rw [he]
    exact hb
  · intro hw ψ hψ
    have he := varying_acceptWith F (fun n => roundsFor (p.eval n))
      (ShiBQP.toBits w) ψ
    change (varying F (fun n => roundsFor (p.eval n))).acceptWith
      (ShiBQP.toBits w) ψ ≤ ((1 : ℝ) / 2) ^ (p.eval w.length)
    rw [he]
    exact h.2 hw ψ hψ

end ShiQMAVariableRounds

#print axioms ShiQMAVariableRounds.polynomialFamily_verifies
