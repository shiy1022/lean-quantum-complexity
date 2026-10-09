import QAlgorithms.Defs.AmplitudeEstimation

/-!
# Nannicini, Chapter 4 (part c): searching when the number of marked items is not known

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Lemma 4.28 (p.92), Theorem 4.29 (p.93), Corollary 4.30 (p.94). Theorem 4.31
(quantum minimum finding, p.96) is not stated (see `HARD.md` of the chunk).

Setting of §4.3.6 (p.91): the setting of §4.2 with `S = H^{⊗n}` (Rem. 4.13) and the phase
reflection `R|j⟩ = (−1)^{f(j)}|j⟩` built from `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩` (p.69), so that
`S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩` with `sin θ = √(|M|/2^n)`, `M = {j : f(j) = 1}`; this `θ` is
the frozen `groverAngle |M| 2^n`. The output states of the amplitude estimation circuit
(Fig. 4.9) on the eigenstates `|ϕ±⟩` are `|ϑ±⟩ = Q_m† (2^{−m/2} Σ_k e^{±2iθk}|k⟩)` (p.92), the
frozen `aeVartheta m (±θ)`. Algorithm 1 (p.94) is the frozen `searchAlg1Weight f` (joint law of
the output, `none` = "no solution", and of the number of applications of `U_f`), with expected
cost `searchAlg1ExpectedCost f`: a round with `m` qubits of precision costs `2^m − 1`
applications of the Grover operator (one `U_f` each) plus one test of `f(j)`, and the final
enumeration costs one application per string tested.
-/

namespace QAlgorithms.Nannicini

open scoped ENNReal

/-- Nannicini p.92–93, Lemma 4.28, in the explicit form its proof derives (p.93):
for `θ ∈ (0, π/2)` (standing assumption of §4.3.6, p.91) and any number `m` of qubits of the
first register, the phase-estimation output states `|ϑ±⟩ = Q_m† (2^{−m/2} Σ_k e^{±2iθk}|k⟩)`
satisfy `|⟨ϑ−|ϑ+⟩| ≤ 1/(2^m sin 2θ)`.

The printed conclusion `|⟨ϑ−|ϑ+⟩| = O(1/(2^m θ))` is false with a constant uniform in `θ`
(for `θ = π/2 − η` with `4η2^m ≪ 1` the overlap is close to `1`), and is only `O(1/2^m)` for
fixed `θ`; the explicit bound, which the proof states right before the `O`-form, is formalized
instead (trap 30; recorded in the chunk's `HARD.md`). -/
theorem aeVartheta_overlap_le (m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ‖inner ℂ (aeVartheta m (-θ)) (aeVartheta m θ)‖ ≤ 1 / ((2 : ℝ) ^ m * Real.sin (2 * θ)) := by
  sorry

/-- Nannicini p.93, Theorem 4.29 (Quantum search; Boyer et al. 1998, Brassard et al. 2002):
there is a constant `C > 0` such that for every `n` and every `f : {0,1}^n → {0,1}`, with
`θ = arcsin √(|M|/2^n)` (`M = {j : f(j) = 1}`), Algorithm 1 (p.94) satisfies:
1. if `θ > 0`, it returns, with probability one, a value `j` with `f(j) = 1`, and the expected
   number of applications of `U_f` is at most `C/θ`;
2. if `θ = 0`, it returns "no solution" (with probability one) and every run uses at most
   `C · 2^n` applications of `U_f`. -/
theorem quantumSearch_unknownCount :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      (0 < groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C / groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n))) ∧
      (groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) = 0 →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        ∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          oc.1 = none ∧ (oc.2 : ℝ) ≤ C * 2 ^ n) := by
  sorry

/-- Nannicini p.94, Corollary 4.30: there is a constant `C > 0` such that for every `n` and every
Boolean function `f : {0,1}^n → {0,1}` with a nonempty set `M = {j : f(j) = 1}` of marked
elements, Algorithm 1 (whose input is only the oracle `U_f`, not `|M|`) returns an element of `M`
with probability one, using at most `C √(2^n/|M|)` applications of `U_f` in expectation. -/
theorem quantumSearch_unknownCount_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      1 ≤ (Finset.univ.filter fun j => f j = true).card →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C * Real.sqrt ((2 : ℝ) ^ n /
            ((Finset.univ.filter fun j => f j = true).card : ℝ))) := by
  sorry

end QAlgorithms.Nannicini
