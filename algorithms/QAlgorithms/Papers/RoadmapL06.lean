import QAlgorithms.Defs.TwoBasisCertification

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.RoadmapL06

open QAlgorithms.TwoBasisCertification

/-- Theorem 1 of Coladangelo, Li, Slote and Wu, *The Power of Two Bases*
(arXiv:2602.11616v1), PDF p.3; oracle model: Definition 1, p.7; test: pp.8–9.

One fixed classical amplitude-oracle program compiles the conditional suffix projector.
The fair choice of a common Z/X prefix basis, one lab copy, and one suffix measurement
are built into `outcomeLaw`. Exact scalar arithmetic and arbitrary one- and two-qubit gates
are the oracle-relative cost model of Lemma 1, p.8. The executed resource counts, including
oracle calls, are polynomial in the total qubit count, uniformly in the target and branch.

We choose gamma = 1 and round the suffix size with `suffixSize`: k = min(n, ceil(2 log_2
(max(2,n)))). Thus r+k=n without truncated subtraction in register types. The full-Hadamard
oracle fiber receives the suffix Hadamard correction (Remark 7, p.10); a zero fiber has
zero accepting effect. The Haar-good set and additive vanishing error work for every
mixed lab state simultaneously. This states p.3's additive soundness, not Theorem 5's
stronger multiplicative implication. -/
theorem robustCertification_twoBases :
    ∃ program : (r k : ℕ) → Bool → Qubits r → AmplitudeProgram (r + k) k,
    ∃ p : Polynomial ℕ, ∃ C : ℝ, ∃ n0 : ℕ, ∃ eta : ℕ → ℝ,
    ∃ good : (n : ℕ) → Set (EuclideanSpace ℂ (Qubits n)),
      program = conditionalMeasurementProgram ∧
      0 < C ∧ 1 ≤ n0 ∧ (∀ n, 0 ≤ eta n) ∧
      Filter.Tendsto eta Filter.atTop (nhds 0) ∧
      (∀ n, MeasurableSet (good n) ∧ ∀ psi ∈ good n, IsState psi) ∧
      (∀ n, n0 ≤ n →
        haarTargetLaw n (good n)ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ n)⁻¹)) ∧
      (∀ r k : ℕ, k = suffixSize (r + k) →
        ∀ psi : EuclideanSpace ℂ (Qubits (r + k)), IsState psi →
        ∀ (had : Bool) (z : Qubits r),
          let result := amplitudeProgramLaw (amplitudeOracle psi) (program r k had z)
            (initialAmplitudeExecution (r + k) k)
          result.failed = false ∧
          result.queries = List.ofFn (fun w : Fin (2 ^ k) =>
            (had, Fin.append z ((bitsEquivFin k).symm w))) ∧
          (∀ j : Fin 4, testResources r k had z (amplitudeOracle psi) j ≤ p.eval (r + k)) ∧
          compiledSuffixEffect r k had z (amplitudeOracle psi) =
            conditionalProjector r k psi had z) ∧
      (∀ r k : ℕ, k = suffixSize (r + k) → n0 ≤ r + k →
        ∀ psi : EuclideanSpace ℂ (Qubits (r + k)), IsState psi → psi ∈ good (r + k) →
        ∀ rho : Matrix (Qubits (r + k)) (Qubits (r + k)) ℂ, IsDensityMatrix rho →
          (pureDensity psi * rho).trace.re ≤ outcomeLaw r k psi rho true ∧
          (1 - (pureDensity psi * rho).trace.re) / 2 - eta (r + k) ≤
            outcomeLaw r k psi rho false) := by sorry

end QAlgorithms.Papers.RoadmapL06
