import QAlgorithms.Defs.CompressedPauliRecovery

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.RoadmapL13

attribute [local instance] Classical.propDecidable

open QAlgorithms.CompressedTomography

/-- Flammia, Gross, Liu and Eisert, arXiv:1205.2300v2, Theorem 1, PDF/printed
page 5; sampling and variational estimators are Eqs. (1)--(4), page 4.
One random sampling event gives both trace-norm bounds, uniformly over PSD
inputs (not necessarily trace one), arbitrary real noise, and all minimizers.
The qualitative failure bound tends to zero with the number of qubits and is
uniform in the admissible rank and sample count; no numerical rate is supplied.
Source clarification: Lasso uses positive regularization `mu > 0`. The printed
noise condition alone allows `mu = 0`, where arbitrary least-squares minimizers
in an unmeasured direction do not obey the asserted recovery bound. This
domain correction and the unnormalized-input reading await independent moderation.
-/
theorem randomPauli_traceNormRecovery :
    ∃ C C0 C1 C0Lasso C1Lasso : ℝ,
      0 < C ∧ 0 < C0 ∧ 0 < C1 ∧ 0 < C0Lasso ∧ 0 < C1Lasso ∧
      ∃ eta : ℕ → ℝ, (∀ n, 0 ≤ eta n ∧ eta n ≤ 1) ∧
        Filter.Tendsto eta Filter.atTop (nhds 0) ∧
        ∀ (n r m : ℕ) (hr : 1 ≤ r ∧ r ≤ 2 ^ n) (hm : 0 < m),
          C * (r : ℝ) * (2 : ℝ) ^ n * Real.log ((2 : ℝ) ^ n) ^ 6 ≤ (m : ℝ) →
          ((PauliDesign.uniformDesign n m).toOuterMeasure
            {P | ∀ (rho : Matrix (Qubits n) (Qubits n) ℂ) (positive : rho.PosSemidef)
                (z : EuclideanSpace ℝ (Fin m)),
              let y := samplingMap P hm rho positive.isHermitian + z
              let tail := traceNorm (rho - bestRankApproximation rho positive r hr)
              (∀ lam : ℝ, specNorm (samplingAdjoint P hm z) ≤ lam →
                (∃ X : Matrix (Qubits n) (Qubits n) ℂ, IsDantzigSelector P hm y lam X) ∧
                ∀ X : Matrix (Qubits n) (Qubits n) ℂ, IsDantzigSelector P hm y lam X →
                  traceNorm (X - rho) ≤ C0 * (r : ℝ) * lam + C1 * tail) ∧
              (∀ mu : ℝ, 0 < mu → specNorm (samplingAdjoint P hm z) ≤ mu / 2 →
                (∃ X : Matrix (Qubits n) (Qubits n) ℂ, IsMatrixLasso P hm y mu X) ∧
                ∀ X : Matrix (Qubits n) (Qubits n) ℂ, IsMatrixLasso P hm y mu X →
                  traceNorm (X - rho) ≤ C0Lasso * (r : ℝ) * mu + C1Lasso * tail)}).toReal
            ≥ 1 - eta n := by sorry

end QAlgorithms.Papers.RoadmapL13
