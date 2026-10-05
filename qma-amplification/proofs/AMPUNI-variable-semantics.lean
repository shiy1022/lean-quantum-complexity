import «AMPUNI-variable-resources»

set_option autoImplicit false
set_option maxHeartbeats 2000000

set_option maxRecDepth 2048

namespace ShiQMAVariableRounds
open ShiShallow ShiClassQMA ShiClassQMAAmp ShiClassQMAAmpX ShiQMAErrorIteration

/-- A verifier's completeness and soundness obligations, independent of uniformity. -/
def Verifies (F : QMAFamily) (L : Language Bool) (c s : ℝ) : Prop :=
  ∀ w : PvsNP.Str,
    (w ∈ L → ∃ ψ : QState (F.wit w.length), Normalized ψ ∧
      c ≤ F.acceptWith (ShiBQP.toBits w) ψ) ∧
    (w ∉ L → ∀ ψ : QState (F.wit w.length), Normalized ψ →
      F.acceptWith (ShiBQP.toBits w) ψ ≤ s)

private theorem acceptWith_ampFamilyX_eq (F : QMAFamily) {n : ℕ} (x : Bits n)
    (ψ : QState ((ampFamily F).wit n)) :
    (ampFamilyX F).acceptWith x ψ = (ampFamily F).acceptWith x ψ := by
  unfold QMAFamily.acceptWith
  change
    (∑ y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))),
      if y ((ampFamily F).out n) then
        ‖runLayered ((ampFamilyX F).circ n) (witnessInputState (ampFamily F) x ψ) y‖ ^ 2
      else 0)
      = ∑ y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))),
          if y ((ampFamily F).out n) then
            ‖runLayered ((ampFamily F).circ n) (witnessInputState (ampFamily F) x ψ) y‖ ^ 2
          else 0
  rw [ampFamilyX_semantically_eq_ampFamily]

theorem one_round_verifies (F : QMAFamily) (L : Language Bool) (c s : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hF : Verifies F L c s) :
    Verifies (ampFamilyX F) L (majorityError c) (majorityError s) := by
  intro w
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hb⟩ := (hF w).1 hw
    obtain ⟨Ψ, hΨ, hamp⟩ :=
      ShiClassQMA.exists_amplified_witness_maj3_ge_of_single_copy_bound
        ampFamily
        ShiClassQMAAmp.ampFamily_resource_identities_and_depth.1
        ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.1
        ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.2.1
        ShiClassQMAAmp.ampFamily_threefold_structure_package.1
        c hc₀ hc₁ F w ⟨ψ, hψ, hb⟩
    refine ⟨Ψ, hΨ, ?_⟩
    calc
      majorityError c = 3 * c ^ 2 - 2 * c ^ 3 := rfl
      _ ≤ (ampFamily F).acceptWith (ShiBQP.toBits w) Ψ := hamp
      _ = (ampFamilyX F).acceptWith (ShiBQP.toBits w) Ψ :=
        (acceptWith_ampFamilyX_eq F _ Ψ).symm
  · intro hw Ψ hΨ
    have hamp := ShiClassQMA.amplified_acceptWith_le_maj3_of_single_copy_bound
      ampFamily
      ShiClassQMAAmp.ampFamily_resource_identities_and_depth.1
      ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.1
      ShiClassQMAAmp.ampFamily_resource_identities_and_depth.2.2.1
      ShiClassQMAAmp.ampFamily_threefold_structure_package.1
      s hs₀ hs₁ F w ((hF w).2 hw) Ψ hΨ
    calc
      (ampFamilyX F).acceptWith (ShiBQP.toBits w) Ψ
          = (ampFamily F).acceptWith (ShiBQP.toBits w) Ψ :=
            acceptWith_ampFamilyX_eq F _ Ψ
      _ ≤ 3 * s ^ 2 - 2 * s ^ 3 := hamp
      _ = majorityError s := rfl

private theorem majorityError_complement (e : ℝ) :
    majorityError (1 - e) = 1 - majorityError e := by
  dsimp [majorityError]
  ring

theorem iter_verifies (F : QMAFamily) (L : Language Bool)
    (hF : Verifies F L ((2 : ℝ) / 3) ((1 : ℝ) / 3)) (r : Nat) :
    Verifies (iter F r) L (1 - error r) (error r) := by
  induction r with
  | zero =>
      change Verifies F L (1 - (1 : ℝ) / 3) ((1 : ℝ) / 3)
      rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num]
      exact hF
  | succ r ih =>
      have he := error_bounds r
      have h := one_round_verifies (iter F r) L (1 - error r) (error r)
        (by linarith) (by linarith) he.1 (by linarith) ih
      simpa only [iter, error, majorityError_complement] using h

/-- The iterated verifier meets a different dyadic target at each input length. -/
theorem iter_verifies_variable_threshold (F : QMAFamily) (L : Language Bool)
    (p : Polynomial ℕ) (hF : Verifies F L ((2 : ℝ) / 3) ((1 : ℝ) / 3)) :
    ∀ w : PvsNP.Str,
      (w ∈ L →
        ∃ ψ : QState ((iter F (roundsFor (p.eval w.length))).wit w.length),
          Normalized ψ ∧
          1 - ((1 : ℝ) / 2) ^ (p.eval w.length) ≤
            (iter F (roundsFor (p.eval w.length))).acceptWith (ShiBQP.toBits w) ψ) ∧
      (w ∉ L →
        ∀ ψ : QState ((iter F (roundsFor (p.eval w.length))).wit w.length),
          Normalized ψ →
          (iter F (roundsFor (p.eval w.length))).acceptWith (ShiBQP.toBits w) ψ ≤
            ((1 : ℝ) / 2) ^ (p.eval w.length)) := by
  intro w
  have h := iter_verifies F L hF (roundsFor (p.eval w.length)) w
  have he := error_roundsFor (p.eval w.length)
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hb⟩ := h.1 hw
    refine ⟨ψ, hψ, ?_⟩
    linarith
  · intro hw ψ hψ
    exact ((h.2 hw) ψ hψ).trans he

end ShiQMAVariableRounds

#print axioms ShiQMAVariableRounds.iter_verifies_variable_threshold
