import «AMPUNI-retained-transducer»
import «INPUT-RETENTION»
import «AMPUNI-error-iteration»

set_option autoImplicit false

namespace ShiQMAUniformIteration
open ShiShallow ShiClassQMA ShiClassQMAAmp ShiClassQMAAmpX ShiQMAErrorIteration

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

/-- The checked encoding transformer works for every admissible pair of thresholds. -/
theorem one_round (c s : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ShiClassQMAU.QMAU c s ⊆ ShiClassQMAU.QMAU (majorityError c) (majorityError s) := by
  intro L hL
  obtain ⟨F, huniform, hwf, hpoly, hverify⟩ := hL
  obtain ⟨g, hg, hmap⟩ := ShiTMNormalizedEntry.retained_encoding_transducer
  obtain ⟨f, hf, hout⟩ := ShiTMInputRetention.uniformQMA_has_length_aware_generator F huniform
  have huni : ShiClassQMAU.UniformQMA (ampFamilyX F) := by
    refine ⟨g ∘ f, PvsNP.polyTimeComputable_comp f g hf hg, ?_⟩
    intro n
    rw [Function.comp_apply, hout, hmap]
  refine ⟨ampFamilyX F,
    huni,
    ampFamilyX_resource_identities_and_regularity.2.2.2.2.1 F hwf,
    ampFamilyX_resource_identities_and_regularity.2.2.2.2.2.1 F hpoly, ?_⟩
  intro w
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hb⟩ := (hverify w).1 hw
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
      s hs₀ hs₁ F w ((hverify w).2 hw) Ψ hΨ
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

/-- Every fixed number of rounds preserves polynomial-time uniformity. -/
theorem fixed_rounds (r : Nat) :
    ShiClassQMAU.QMAU ((2 : ℝ) / 3) ((1 : ℝ) / 3) ⊆
      ShiClassQMAU.QMAU (1 - error r) (error r) := by
  intro L hL
  induction r with
  | zero =>
      change L ∈ ShiClassQMAU.QMAU (1 - (1 : ℝ) / 3) ((1 : ℝ) / 3)
      rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num]
      exact hL
  | succ r ih =>
      have he := error_bounds r
      have h := one_round (1 - error r) (error r)
        (by linarith) (by linarith) he.1 (by linarith) ih
      rw [majorityError_complement] at h
      exact h

private theorem thresholds_mono {c s c' s' : ℝ} (hc : c' ≤ c) (hs : s ≤ s') :
    ShiClassQMAU.QMAU c s ⊆ ShiClassQMAU.QMAU c' s' := by
  rintro L ⟨F, hu, hw, hp, hv⟩
  refine ⟨F, hu, hw, hp, ?_⟩
  intro w
  constructor
  · intro hmem
    obtain ⟨ψ, hψ, hacc⟩ := (hv w).1 hmem
    exact ⟨ψ, hψ, hc.trans hacc⟩
  · intro hmem ψ hψ
    exact ((hv w).2 hmem ψ hψ).trans hs

/-- Arbitrarily small fixed dyadic error, with the encoding transformer supplied.
Here `m` is fixed for the family; this is not an input-dependent iteration theorem. -/
theorem fixed_dyadic_error (m : Nat) :
    ShiClassQMAU.QMAU ((2 : ℝ) / 3) ((1 : ℝ) / 3) ⊆
      ShiClassQMAU.QMAU (1 - ((1 : ℝ) / 2) ^ m) (((1 : ℝ) / 2) ^ m) := by
  intro L hL
  have h := fixed_rounds (roundsFor m) hL
  have he := error_roundsFor m
  exact thresholds_mono (by linarith) he h

end ShiQMAUniformIteration

-- The inherited reference-theorem assumptions must remain visible.
#print axioms ShiQMAUniformIteration.fixed_dyadic_error
