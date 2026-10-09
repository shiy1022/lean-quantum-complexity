import QAlgorithms.Defs.AmplitudeEstimation

/-!
# Nannicini, Chapter 3 (§3.2.2–§3.3.2): phase estimation on non-eigenstates, iterative phase
estimation

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages). Phases are in full turns (`φ ∈ [0, 1)` stands for the eigenvalue `e^{2πiφ}`); the
phase estimation circuit of Fig. 3.6 with `m` estimation qubits is the frozen
`phaseEstimationState m U ψ`, whose first register `p` is read as `0.p = p / 2^m`; precision is
the distance on the circle `circDist` (p.62: `min{|φ − 0.p|, 1 − |φ − 0.p|}`).
-/

namespace QAlgorithms.Nannicini

open QAlgorithms

/-- Nannicini p.63, Proposition 3.14 (phase estimation on an inexact eigenstate): suppose
phase estimation with `m` estimation qubits (Fig. 3.6) has precision `ε` and probability of
success `≥ 1 − δ`, i.e. on every unit eigenvector `v` of `U` with eigenvalue `e^{2πiφ}`,
`φ ∈ [0, 1)`, the output `p` satisfies `circDist (0.p) φ < ε` with probability `≥ 1 − δ`
(the guarantee of Thm. 3.9, p.62). Let `ψ*` be a unit eigenvector with eigenvalue `e^{2πiφ*}`
and `ξ` any state. Then running the circuit on `ξ` outputs `p*` with `circDist (0.p*) φ* < ε`
with probability at least `(1 − δ) |⟨ξ|ψ*⟩|²`. -/
theorem phaseEstimation_inexactEigenstate (n m : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1)
    (hQPE : ∀ (v : EuclideanSpace ℂ (Qubits n)) (φ : ℝ), IsState v → 0 ≤ φ → φ < 1 →
      act U v = Complex.exp (2 * Real.pi * Complex.I * (φ : ℂ)) • v →
      probEvent (phaseEstimationState m U v)
        (fun z => circDist ((bitsToNat z.1 : ℝ) / (2 : ℝ) ^ m) φ < ε) ≥ 1 - δ)
    (psiStar : EuclideanSpace ℂ (Qubits n)) (phiStar : ℝ) (hpsi : IsState psiStar)
    (hphi0 : 0 ≤ phiStar) (hphi1 : phiStar < 1)
    (heig : act U psiStar = Complex.exp (2 * Real.pi * Complex.I * (phiStar : ℂ)) • psiStar)
    (xi : EuclideanSpace ℂ (Qubits n)) (hxi : IsState xi) :
    probEvent (phaseEstimationState m U xi)
        (fun z => circDist ((bitsToNat z.1 : ℝ) / (2 : ℝ) ^ m) phiStar < ε) ≥
      (1 - δ) * ‖inner ℂ xi psiStar‖ ^ 2 := by sorry

/-- Nannicini p.66, Proposition 3.16 (combining sine and cosine estimates), **corrected**
(trap 30, see `HARD.md`): there is a rule `F` turning estimates `c̃, s̃` of `cos φ, sin φ` into an
angle estimate `φ̃ = F c̃ s̃` such that, for every `0 ≤ η < π/2` and `φ ∈ [0, 2π]`, the errors
`|c̃ − cos φ| ≤ sin η / √2` and `|s̃ − sin φ| ≤ sin η / √2` imply that `φ̃` is within `η` of `φ`
modulo `2π`. The page states `η ≤ π/2` and the plain distance `|φ̃ − φ|`; both readings are
false (at `η = π/2` the estimates `(0, 0)` fit `φ = π/4, 3π/4, 5π/4, 7π/4`; `φ = 0` and `φ = 2π`
have the same exact estimates), while angles are defined modulo `2π` (p.66). The angular
distance is `2π · circDist (φ̃ / 2π) (φ / 2π)`. -/
theorem angle_from_cos_sin_estimates :
    ∃ F : ℝ → ℝ → ℝ, ∀ η : ℝ, 0 ≤ η → η < Real.pi / 2 →
      ∀ φ : ℝ, 0 ≤ φ → φ ≤ 2 * Real.pi → ∀ c s : ℝ,
        |c - Real.cos φ| ≤ Real.sin η / Real.sqrt 2 →
        |s - Real.sin φ| ≤ Real.sin η / Real.sqrt 2 →
        2 * Real.pi * circDist (F c s / (2 * Real.pi)) (φ / (2 * Real.pi)) ≤ η := by sorry

/-- Nannicini p.66, Proposition 3.17 (correctness of iterative phase estimation), **corrected**
(trap 30, see `HARD.md`). Let `φ ∈ [0, 1)`, `h = q − 2`, and let `ω i` be the estimate of the
angle `2^{i−1} φ` (in turns) used at step `i`. The digits `p_1 … p_{h+2}` are those computed by
the algorithm of §3.3.2 (`ipeDigits h ω`: initialization rounds `ω_h` to the closest multiple of
`1/8`, giving `p_h p_{h+1} p_{h+2}`; step `j = h−1, …, 1` sets `p_j = 0` iff
`|0.0 p_{j+1} p_{j+2} − ω_j| < 1/4` on the circle). If at steps `i = h, …, j` the estimate `ω_i`
is within `1/16` of `2^{i−1} φ`, then `0.p_j … p_{h+2}` is within `2^{−(h+3−j)}` of `2^{j−1} φ`.
All distances are on the circle (angles are known modulo `1`, p.66), and the bound is `≤`
rather than the page's `<`, which already fails at the base case (`ω_h = 1/16`). -/
theorem iterativePhaseEstimation_digits (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (h : ℕ)
    (ω : ℕ → ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ h)
    (hω : ∀ i, j ≤ i → i ≤ h → circDist (ω i) ((2 : ℝ) ^ (i - 1) * φ) ≤ 1 / 16) :
    circDist (binFracFrom (ipeDigits h ω) j (h + 2)) ((2 : ℝ) ^ (j - 1) * φ) ≤
      ((2 : ℝ) ^ (h + 3 - j))⁻¹ := by sorry

end QAlgorithms.Nannicini
