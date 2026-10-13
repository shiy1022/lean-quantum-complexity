import QAlgorithms.Defs.RetainedStabilizerLearners

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL16

open QAlgorithms.Stabilizer QAlgorithms.StabilizerLearning

/-- Chang, Caro, Larocca and West, *Sample-optimal learning of stabilizer states*,
arXiv:2609.10974v1, Theorem 1, PDF p.2; operational and time accounting on pp.3,5,12-13,21-22.
The implicit qubit domain is `n >= 1`, as used by the lower-bound proof on p.7:
at `n = 0` the unique physical state needs no copies, so the printed lower bound fails.
`copyComplexity` is the unrestricted, worst-case POVM minimum in the extended naturals.
Writing the lower bound with `+ 3` avoids truncated natural subtraction. The efficient witness
retains its input registers through adaptive trials; its time counts elementary Clifford+T
gates, measurements, coins, Boolean operations, storage initialization and tableau decoding.
Success means a valid signed stabilizer tableau specifying the input density matrix, so it
does not depend on a vector's global phase or a particular choice of generators.
The sample bounds and worst-case success hold throughout the domain; only the uniform
asymptotic runtime bound has a threshold. Natural logarithms are used only in runtime,
and base two is retained in the exact sample ceiling. -/
theorem sampleOptimal_stabilizerLearning :
    ∃ C : ℝ, 0 < C ∧ ∃ threshold : ℝ, 1 ≤ threshold ∧
      ∀ (n : ℕ) (delta : ℝ), 1 ≤ n → 0 < delta → delta < 1 / 8 →
        let c : ℕ := ⌈Real.logb 2 delta⁻¹⌉₊
        ((n + c : ℕ) : ℕ∞) ≤ copyComplexity n delta + 3 ∧
        copyComplexity n delta ≤ ((n + c + 4 : ℕ) : ℕ∞) ∧
        ∃ L : RetainedCopyLearner n,
          L.copies ≤ n + c + 4 ∧
          (∀ psi : EuclideanSpace ℂ (Qubits n), ∀ hpsi : IsStabilizerState psi,
            (open Classical in
              ∑ result : Fin (n * (2 * n + 2)) → Bool,
                if IsValidTableau (decodeTableau n (List.ofFn result)) ∧
                    tableauProjector (decodeTableau n (List.ofFn result)) = pureDensity psi
                then retainedLearnerLaw L psi hpsi.1 result else 0) ≥ 1 - delta) ∧
          (threshold ≤ (n : ℝ) + Real.log delta⁻¹ →
            (L.time : ℝ) ≤ C * (n : ℝ) * ((n : ℝ) + Real.log delta⁻¹) ^ 4) := by sorry

end QAlgorithms.Papers.RoadmapL16
