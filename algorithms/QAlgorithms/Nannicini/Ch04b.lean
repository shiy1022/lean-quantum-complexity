import QAlgorithms.Defs.AmplitudeEstimation

/-!
# Nannicini, Chapter 4 (part b): amplitude estimation

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Proposition 4.15 (p.84), Proposition 4.19 (p.87), Proposition 4.21 (p.88),
Corollary 4.22 (p.88).

Setting of §4.3 (p.83). The input is an `n`-qubit unitary circuit `S` with
`S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩`, `⟨ψ_G|ψ_B⟩ = 0`, `θ ∈ [0, π/2]`, where `ψ_G`, `ψ_B` are states,
and the reflection `R` (the controlled circuit `CR` with its control set) with `R|ψ_G⟩ = −|ψ_G⟩`,
`R|ψ_B⟩ = |ψ_B⟩`. The Grover operator is `G = S F S† R` with `F = 2|0⟩⟨0| − I = reflAt 0`,
the frozen `ampAmpIterate S R 0`. The amplitude estimation circuit of §4.3.3 / Fig. 4.9 is the
frozen `aeState m S R` (phase estimation of `G` on `S|0⟩` with `m` qubits), and its output angle
`θ̃` read off the measured first register `b` is the frozen `aeAngle b`.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.84, Proposition 4.15: in the setting of §4.3 (p.83: `S` an `n`-qubit unitary,
`S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩` with `ψ_G`, `ψ_B` orthogonal states and `θ ∈ [0, π/2]`; `R` a
unitary with `R|ψ_G⟩ = −|ψ_G⟩`, `R|ψ_B⟩ = |ψ_B⟩`; `F = 2|0⟩⟨0| − I`), the states
`|ϕ±⟩ = (1/√2)(|ψ_G⟩ ± i|ψ_B⟩)` are orthogonal eigenstates of `S F S† R` with eigenvalues
`e^{2iθ}` and `e^{−2iθ}` respectively. -/
theorem groverOperator_eigenstates {n : ℕ} (S R : Matrix (Qubits n) (Qubits n) ℂ)
    (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ)
    (hS : S ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hR : R ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hG : IsState psiG) (hB : IsState psiB) (horth : inner ℂ psiG psiB = 0)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (hprep : act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB)
    (hRG : act R psiG = -psiG) (hRB : act R psiB = psiB) :
    let phiPlus := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG + Complex.I • psiB)
    let phiMinus := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG - Complex.I • psiB)
    IsState phiPlus ∧ IsState phiMinus ∧ inner ℂ phiPlus phiMinus = 0 ∧
      act (ampAmpIterate S R 0) phiPlus = Complex.exp (2 * Complex.I * θ) • phiPlus ∧
      act (ampAmpIterate S R 0) phiMinus = Complex.exp (-(2 * Complex.I * θ)) • phiMinus := by
  sorry

/-- Nannicini p.87, Proposition 4.19 (Lem. 7 in Brassard et al. 2002): let `a = sin²θ` and
`ã = sin²θ̃` with `0 ≤ θ, θ̃ ≤ 2π`. Then `|θ − θ̃| ≤ ϵ` implies
`|a − ã| ≤ 2ϵ √(a(1 − a)) + ϵ²`. -/
theorem sinSq_angle_error (θ θt ε : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 2 * Real.pi)
    (hθt0 : 0 ≤ θt) (hθt1 : θt ≤ 2 * Real.pi) (h : |θ - θt| ≤ ε) :
    |Real.sin θ ^ 2 - Real.sin θt ^ 2| ≤
      2 * ε * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) + ε ^ 2 := by
  sorry

/-- Nannicini p.88, Proposition 4.21 (Thm. 12 in Brassard et al. 2002): in the setting of §4.3
(p.83: `S` an `n`-qubit unitary, `S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩` with `ψ_G`, `ψ_B` orthogonal
states and `θ ∈ [0, π/2]`; `R` a unitary with `R|ψ_G⟩ = −|ψ_G⟩`, `R|ψ_B⟩ = |ψ_B⟩`), apply the
amplitude estimation algorithm of §4.3.3 (p.86, Fig. 4.9) with `m` qubits for phase estimation:
prepare `|0⟩_m ⊗ S|0⟩_n`, run phase estimation of `G = S F S† R`, measure the first register to
get `b`, and return `θ̃ = π(1 − 0.b)` if `b_1 = 1`, `θ̃ = π·0.b` otherwise. With `a = sin²θ` and
`ã = sin²θ̃`, the outcome satisfies `|a − ã| ≤ 2π√(a(1 − a))/2^m + π²/2^{2m}` (4.8) with
probability at least `8/π²`. -/
theorem amplitudeEstimation_error {n : ℕ} (m : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ)
    (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ)
    (hS : S ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hR : R ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hG : IsState psiG) (hB : IsState psiB) (horth : inner ℂ psiG psiB = 0)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (hprep : act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB)
    (hRG : act R psiG = -psiG) (hRB : act R psiB = psiB) :
    8 / Real.pi ^ 2 ≤ probEvent (aeState m S R) fun z =>
      |Real.sin θ ^ 2 - Real.sin (aeAngle z.1) ^ 2| ≤
        2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) / (2 : ℝ) ^ m +
          Real.pi ^ 2 / (2 : ℝ) ^ (2 * m) := by
  sorry

/-- Nannicini p.88, Corollary 4.22: to estimate the probability `sin²θ` of obtaining `|ψ_G⟩` from a
measurement of `S|0⟩` with absolute error at most `ϵ` by amplitude estimation, it suffices to use
`m = O(log 1/ϵ)` qubits for phase estimation, leading to `O(1/ϵ)` queries to the input unitaries
`S` and `CR`. Formally: there is a constant `C > 0` such that for every `ϵ ∈ (0, 1)` there is an
`m` (chosen before the input `n, S, R, θ, ψ_G, ψ_B`) with `m ≤ C (log₂(1/ϵ) + 1)` and with the
number `3(2^m − 1) + 1` of calls to `S`, `S†` and `CR` made by the `m`-qubit circuit (p.86: `2^m − 1`
controlled Grover operators, each with one `S`, one `S†` and one `CR`, plus the initial `S`) at
most `C/ϵ`, such that for every input of §4.3 the estimate `ã = sin²θ̃` of Prop. 4.21's algorithm
satisfies `|sin²θ − ã| ≤ ϵ` with probability at least `8/π²` (the success probability of
Prop. 4.21, from which the corollary follows). -/
theorem amplitudeEstimation_complexity :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ m : ℕ, (m : ℝ) ≤ C * (Real.logb 2 (1 / ε) + 1) ∧
        ((3 * (2 ^ m - 1) + 1 : ℕ) : ℝ) ≤ C / ε ∧
        ∀ (n : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ)
          (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ),
          S ∈ Matrix.unitaryGroup (Qubits n) ℂ → R ∈ Matrix.unitaryGroup (Qubits n) ℂ →
          IsState psiG → IsState psiB → inner ℂ psiG psiB = 0 →
          0 ≤ θ → θ ≤ Real.pi / 2 →
          act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB →
          act R psiG = -psiG → act R psiB = psiB →
          8 / Real.pi ^ 2 ≤ probEvent (aeState m S R) fun z =>
            |Real.sin θ ^ 2 - Real.sin (aeAngle z.1) ^ 2| ≤ ε := by
  sorry

end QAlgorithms.Nannicini
