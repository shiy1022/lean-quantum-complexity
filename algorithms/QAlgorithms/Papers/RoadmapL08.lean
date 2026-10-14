import QAlgorithms.Defs.SparsePauliNoiseAlgorithms

noncomputable section

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapL08

open QAlgorithms.SparsePauliNoise

/-- Harper, Yu and Flammia, arXiv:2007.07901v2, Theorem 1 (PDF pp.8,15),
with Assumptions 1 (p.7), Definition 1 (pp.12,15), and Algorithms 2--4.
The public construction precedes the unknown support/rates and Gaussian observations.
The named program is subsampling followed by peeling with its actual bin detector.
Probability averages over exact-size random support and independent public design/noise.

Source interpretation independently approved in wave7/defs/MODERATION-r2.md:
Algorithm 2's dimensionally inconsistent J_b is replaced by the separate ordinary b-bit
WHT and query addresses J_n M_c l+d; offsets have length 2n, as Eq.(13) requires.
Peeled source bins are retired, as the graph description on pp.13,18 requires.
Algorithm 3's return is after BOTH loops on the rendered p.14 (contrary to the plan note).
The claim retains 2*xi/sqrt(B), exact support recovery, and exponential failure.
No favorable graph, successful prior detection, independence of bin noise, accuracy,
or runtime is assumed. Concrete code/decoder synthesis is existential, not supplied
as a hypothesis. Classical work is the frozen arithmetic/indexing instruction count. -/
theorem sparsePauliRecovery :
    ∀ delta : ℝ, 0 < delta → delta < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ beta : ℝ, 0 < beta ∧
    ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∃ construct : (n : {n : ℕ // n0 ≤ n}) → (s : ℕ) → RecoveryDesign n.val,
    ∀ n s : ℕ, ∀ (hn : n0 ≤ n) (hs : 1 < s)
      (hfeasible : s ≤ Fintype.card (Label n)),
    (s : ℝ) = (4 : ℝ) ^ (delta * n) →
    let D := construct ⟨n, hn⟩ s
    let B := 2 ^ D.b
    (s : ℝ) ≤ B ∧ (B : ℝ) ≤ C * s ∧
    (D.groups : ℝ) ≤ C ∧ n ≤ D.P1 ∧ 2 * n ≤ D.P2 ∧
    ((D.P1 + D.P2 : ℕ) : ℝ) ≤ C * n ∧
    (D.iterations : ℝ) ≤ C * n ∧
    Function.Injective D.code.mulVec ∧
    (∀ message : Fin (n + n) → ZMod 2, message ≠ 0 →
      beta * D.P2 ≤ (hammingNorm (D.code.mulVec message) : ℝ)) ∧
    (∀ word : Fin D.P2 → ZMod 2,
      let memory : ℕ → ℝ := fun i =>
        if hi : i < D.P2 then (if word ⟨i, hi⟩ = 1 then 1 else 0) else 0
      ∀ state ∈ (execution (fun _ => 0) D.decoder ⟨memory, [], [], 0, false⟩).support,
        state.failed = false ∧ (state.work : ℝ) ≤ C * n ∧
        ∀ label : Label n,
          (hammingDist word (D.code.mulVec (Fin.append label.2 label.1)) : ℝ) ≤
              beta * D.P2 →
          ∀ i : Fin (n + n), state.memory (D.P2 + i.val) =
            if Fin.append label.1 label.2 i = 1 then 1 else 0) ∧
    ∀ xi : ℝ, ∀ hxi : 0 ≤ xi, ∀ epsilon0 : ℝ, 0 < epsilon0 →
    xi ^ 2 ≤ min ((B : ℝ) / (s : ℝ) ^ 2) 1 →
    2 * xi / Real.sqrt B ≤ epsilon0 →
    let Seed := (Fin D.groups → Matrix (Fin (n + n)) (Fin D.b) (ZMod 2)) ×
      (Fin D.groups → Fin D.P1 → Label n)
    let design : Seed → RecoveryDesign n := fun seed =>
      { D with hashMatrix := seed.1, randomOffsets := seed.2 }
    let program : Seed → OracleProgram n := fun seed =>
      (subsamplingProgram (design seed)).then (peelingProgram (design seed) xi hxi)
    (∀ seed : Seed, ∀ observations : Label n → ℝ,
      ∀ state ∈ (execution observations (program seed) ⟨0, [], [], 0, false⟩).support,
        (state.trace.length : ℝ) ≤ C * s * n ∧
        (state.work : ℝ) ≤ C * s * n ^ 2) ∧
    ∀ rates : (K : {K : Finset (Label n) // K.card = s}) →
        AdmissibleRates n s K.val epsilon0,
    (∀ K seed, Measurable (fun observations : Label n → ℝ =>
      (execution observations (program seed) ⟨0, [], [], 0, false⟩).toOuterMeasure
        {state | recoveryEvent (design seed) (rates K).rate xi hxi state})) ∧
    (∑ K : {K : Finset (Label n) // K.card = s},
      (supportLaw n s (lt_trans Nat.zero_lt_one hs) hfeasible K) *
        ∑ seed : Seed, (PMF.uniformOfFintype Seed seed) *
          ∫⁻ observations : Label n → ℝ,
            (execution observations (program seed) ⟨0, [], [], 0, false⟩).toOuterMeasure
              {state | recoveryEvent (design seed) (rates K).rate xi hxi state}
            ∂noisyEigenvalueLaw (rates K).rate (rates K).distribution xi hxi) ≥
      ENNReal.ofReal (1 - Real.exp (-c * n)) := by sorry

end QAlgorithms.Papers.RoadmapL08
