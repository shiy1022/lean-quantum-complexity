import QAlgorithms.Defs.DirectFidelityEstimation

noncomputable section

namespace QAlgorithms.Papers.RoadmapL12

open QAlgorithms.DirectFidelity

/-- Flammia–Liu, Direct Fidelity Estimation from Few Pauli Measurements,
arXiv:1104.4695v3, PDF p.2, equations (3)–(10); assumptions on p.1 and concentration
argument on p.6. The target is pure and normalized; the laboratory state may be mixed.
The experiment draws exactly `settingCount` Pauli settings independently with replacement,
and measures each on `repetitions` fresh copies. Its closed interval contains the source's
squared fidelity `Re Tr(rho * sigma)` with probability at least `1 - 2 * delta`.
The copy bound is in expectation, including the per-setting bound (9).
The appendix's (13)–(14) must restrict the second moment to nonzero target coefficients;
the resulting inequality suffices for this unchanged guarantee. -/
theorem directFidelityEstimation_guarantee {n : ℕ}
    (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi)
    (sigma : Matrix (Qubits n) (Qubits n) ℂ) (hsigma : IsDensityMatrix sigma)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1) :
    let rho := pureDensity psi
    let ell := settingCount eps delta heps hdelta
    (open Classical in
      ∑ e : Experiment rho eps delta heps hdelta,
        if (rho * sigma).trace.re ∈
            Set.Icc (estimate rho eps delta heps hdelta e - 2 * eps)
              (estimate rho eps delta heps hdelta e + 2 * eps)
        then experimentLaw psi hpsi sigma hsigma eps delta heps hdelta e else 0) ≥
          1 - 2 * delta ∧
    (∀ settings : Fin ell → characteristicSupport rho,
      (Finset.univ.image settings).card ≤ ell) ∧
    (∑ k : characteristicSupport rho,
      pauliCharacteristic rho k.val ^ 2 *
        (repetitions rho eps delta heps hdelta k : ℝ)) ≤
          1 + (2 * (2 : ℝ) ^ n / ((ell : ℝ) * eps ^ 2)) * Real.log (2 / delta) ∧
    (∑ settings : Fin ell → characteristicSupport rho,
      (∏ i, (importanceLaw psi hpsi (settings i)).toReal) *
        (copyCount rho eps delta heps hdelta settings : ℝ)) ≤
          1 + 1 / (eps ^ 2 * delta) + (2 * (2 : ℝ) ^ n / eps ^ 2) * Real.log (2 / delta)
    := by sorry

end QAlgorithms.Papers.RoadmapL12
