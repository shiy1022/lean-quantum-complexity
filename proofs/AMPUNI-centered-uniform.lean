import «AMPUNI-constructive-uniform-amplification»
import «AMPUNI-gap-dominating-schedule»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace ShiQMAGeneralGap
open ShiShallow ShiClassQMA ShiClassQMAU ShiClassQMAAmp ShiClassQMAAmpX
  ShiQMAErrorIteration ShiQMACenteredGap ShiQMAVariableRounds ShiQMAConstructiveSchedule

/-- Completeness and soundness on one input; the no case includes all normalized witnesses. -/
def VerifiesAt (F : QMAFamily) (L : Language Bool) (c s : ℝ) (w : PvsNP.Str) : Prop :=
  (w ∈ L → ∃ ψ : QState (F.wit w.length), Normalized ψ ∧
    c ≤ F.acceptWith (ShiBQP.toBits w) ψ) ∧
  (w ∉ L → ∀ ψ : QState (F.wit w.length), Normalized ψ →
    F.acceptWith (ShiBQP.toBits w) ψ ≤ s)

/-- Register-aware verification with thresholds depending on input length. -/
def VerifiesWith (F : QMAFamily) (L : Language Bool) (c s : Nat → ℝ) : Prop :=
  ∀ w : PvsNP.Str, VerifiesAt F L (c w.length) (s w.length) w

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

theorem one_round_at (F : QMAFamily) (L : Language Bool) (w : PvsNP.Str) (c s : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hF : VerifiesAt F L c s w) :
    VerifiesAt (ampFamilyX F) L (majorityError c) (majorityError s) w := by
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hb⟩ := hF.1 hw
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
      s hs₀ hs₁ F w (hF.2 hw) Ψ hΨ
    calc
      (ampFamilyX F).acceptWith (ShiBQP.toBits w) Ψ
          = (ampFamily F).acceptWith (ShiBQP.toBits w) Ψ :=
            acceptWith_ampFamilyX_eq F _ Ψ
      _ ≤ 3 * s ^ 2 - 2 * s ^ 3 := hamp
      _ = majorityError s := rfl

theorem iter_centered_at (F : QMAFamily) (L : Language Bool) (w : PvsNP.Str)
    (d : ℝ) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    (hF : VerifiesAt F L (1 / 2 + d) (1 / 2 - d) w) (r : Nat) :
    VerifiesAt (iter F r) L (1 / 2 + biasIter d r) (1 / 2 - biasIter d r) w := by
  induction r with
  | zero => exact hF
  | succ r ih =>
    have hb := biasIter_bounds hd₀ hd₁ r
    have h := one_round_at (iter F r) L w
      (1 / 2 + biasIter d r) (1 / 2 - biasIter d r)
      (by linarith) (by linarith) (by linarith) (by linarith) ih
    have hlo : majorityError (1 / 2 - biasIter d r) =
        1 / 2 - biasStep (biasIter d r) := by
      dsimp [majorityError, biasStep]
      ring
    simpa only [iter, biasIter, majority_centered, hlo] using h

theorem verifiesAt_mono {F : QMAFamily} {L : Language Bool} {w : PvsNP.Str}
    {c s c' s' : ℝ} (hF : VerifiesAt F L c s w) (hc : c' ≤ c) (hs : s ≤ s') :
    VerifiesAt F L c' s' w := by
  constructor
  · intro hw
    obtain ⟨ψ, hψ, hyes⟩ := hF.1 hw
    exact ⟨ψ, hψ, hc.trans hyes⟩
  · intro hw ψ hψ
    exact (hF.2 hw ψ hψ).trans hs

/-- Transfer pointwise semantics without unfolding a concrete schedule inside
large dependent witness and circuit types. -/
theorem varying_verifiesWith (F : QMAFamily) (L : Language Bool)
    (R : Nat → Nat) (c s : Nat → ℝ)
    (h : ∀ w, VerifiesAt (iter F (R w.length)) L (c w.length) (s w.length) w) :
    VerifiesWith (varying F R) L c s := by
  intro w
  exact h w

/-- The existing concrete family now amplifies length-dependent centered gaps. -/
theorem constructiveFamily_centered (F : QMAFamily) (L : Language Bool)
    (d : Nat → ℝ) (q p : Polynomial ℕ)
    (hd₀ : ∀ n, 0 ≤ d n) (hd₁ : ∀ n, d n ≤ 1 / 2)
    (hgap : ∀ n, (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d n)
    (hF : VerifiesWith F L (fun n => 1 / 2 + d n) (fun n => 1 / 2 - d n)) :
    VerifiesWith (constructiveFamily F (gapPolynomial q p)) L
      (fun n => 1 - ((1 : ℝ) / 2) ^ (p.eval n))
      (fun n => ((1 : ℝ) / 2) ^ (p.eval n)) := by
  apply varying_verifiesWith F L (rounds (gapPolynomial q p))
  intro w
  have h := iter_centered_at F L w (d w.length) (hd₀ _) (hd₁ _) (hF w)
    (rounds (gapPolynomial q p) w.length)
  have hb := existing_rounds_suffice (hd₀ _) (hd₁ _) q p w.length (hgap _)
  exact verifiesAt_mono h (by linarith only [hb]) (by linarith only [hb])

/-- Uniform, polynomial-resource amplification for arbitrary length-dependent
centered inverse-polynomial gaps. No assumed encoding transducer is required. -/
theorem centered_gap_amplification (F : QMAFamily) (L : Language Bool)
    (huniform : UniformQMA F) (hwell : ShiBQP.WellFormed F.toFamily)
    (hpoly : ShiBQP.PolyBounded F.toFamily)
    (d : Nat → ℝ) (q p : Polynomial ℕ)
    (hd₀ : ∀ n, 0 ≤ d n) (hd₁ : ∀ n, d n ≤ 1 / 2)
    (hgap : ∀ n, (1 / 6 : ℝ) ≤ (↑(q.eval n) : ℝ) * d n)
    (hF : VerifiesWith F L (fun n => 1 / 2 + d n) (fun n => 1 / 2 - d n)) :
    ∃ G : QMAFamily,
      UniformQMA G ∧ ShiBQP.WellFormed G.toFamily ∧ ShiBQP.PolyBounded G.toFamily ∧
      VerifiesWith G L (fun n => 1 - ((1 : ℝ) / 2) ^ (p.eval n))
        (fun n => ((1 : ℝ) / 2) ^ (p.eval n)) := by
  exact ⟨constructiveFamily F (gapPolynomial q p),
    constructiveFamily_uniform F _ huniform hwell hpoly,
    constructiveFamily_wellFormed F _ hwell,
    constructiveFamily_polyBounded F _ hpoly,
    constructiveFamily_centered F L d q p hd₀ hd₁ hgap hF⟩

end ShiQMAGeneralGap

-- This source uses original reference declarations. The separately reconstructed
-- public endpoint is audited in AMPUNI-centered-uniform-closed.
#print axioms ShiQMAGeneralGap.centered_gap_amplification
