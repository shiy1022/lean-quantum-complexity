import QAlgorithms.Defs.Search

/-!
# de Wolf, Chapter 7: Grover's search algorithm and amplitude amplification

Source: R. de Wolf, *Quantum Computing: Lecture Notes*, Chapter 7, PDF pp.65–70.
-/

namespace QAlgorithms.DeWolf

open QAlgorithms

/-- de Wolf §7.2, PDF pp.65–68 (unnumbered): Grover's algorithm with a known number of
solutions.

Let `N = 2^n`, `x ∈ {0,1}^N` with `t ≥ 1` solutions (`t` the Hamming weight of `x`), and
`θ = arcsin √(t/N)`. Grover's algorithm prepares `H^{⊗n}|0^n⟩`, applies the Grover iterate
`G = H^{⊗n} R_0 H^{⊗n} O_{x,±}` (one phase query each) `k` times and measures.
1. For every `k`, the probability of measuring a solution is `P_k = sin²((2k+1)θ)`.
2. If `k` is an integer closest to `k̃ = π/(4θ) − 1/2`, then `1 − P_k ≤ t/N` and the number of
   queries satisfies `k ≤ π/(4θ) ≤ (π/4)√(N/t)`. -/
theorem grover_known_t (n : ℕ) (x : Qubits n → Bool) (ht : 1 ≤ hammingWeight x) :
    (∀ k : ℕ, groverSuccessProb x k =
        Real.sin ((2 * k + 1) * groverAngle (hammingWeight x) (2 ^ n)) ^ 2) ∧
    ∀ k : ℕ, |(k : ℝ) - (Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) - 1 / 2)| ≤ 1 / 2 →
      1 - (hammingWeight x : ℝ) / ((2 ^ n : ℕ) : ℝ) ≤ groverSuccessProb x k ∧
      (k : ℝ) ≤ Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) ∧
      Real.pi / (4 * groverAngle (hammingWeight x) (2 ^ n)) ≤
        Real.pi / 4 * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (hammingWeight x : ℝ)) := by
  sorry

/-- de Wolf §7.3, PDF pp.68–69 (unnumbered): amplitude amplification.

Let `A` be a unitary on `m` qubits with `A|0^m⟩ = √p |ψ₁⟩ + √(1−p) |ψ₀⟩`, where `ψ₁, ψ₀` are
orthogonal unit vectors and `0 < p ≤ 1`, and let `R_G` be a unitary with `R_G ψ₁ = −ψ₁`,
`R_G ψ₀ = ψ₀`. Put `θ = arcsin √p` and `Q = A R_0 A^{-1} R_G` (`A^{-1} = A^*`).
1. For every `k`, `Q^k A|0^m⟩ = sin((2k+1)θ) ψ₁ + cos((2k+1)θ) ψ₀`.
2. If `k` is an integer closest to `π/(4θ) − 1/2`, then `k ≤ π/(4θ) ≤ π/(4√p)` and the
   probability `|⟨ψ₁|Q^k A|0^m⟩|²` of the good state is at least `1 − p`. -/
theorem amplitudeAmplification (m : ℕ) (A RG : Matrix (Qubits m) (Qubits m) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits m) ℂ) (hRG : RG ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (ψ1 ψ0 : EuclideanSpace ℂ (Qubits m)) (hψ1 : IsState ψ1) (hψ0 : IsState ψ0)
    (horth : inner ℂ ψ1 ψ0 = 0) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hAψ : act A (zeroKet m) =
      (Real.sqrt p : ℂ) • ψ1 + (Real.sqrt (1 - p) : ℂ) • ψ0)
    (hRG1 : act RG ψ1 = -ψ1) (hRG0 : act RG ψ0 = ψ0) :
    (∀ k : ℕ, act (ampAmpIterate A RG (0 : Qubits m) ^ k) (act A (zeroKet m)) =
        (Real.sin ((2 * k + 1) * Real.arcsin (Real.sqrt p)) : ℂ) • ψ1 +
          (Real.cos ((2 * k + 1) * Real.arcsin (Real.sqrt p)) : ℂ) • ψ0) ∧
    ∀ k : ℕ, |(k : ℝ) - (Real.pi / (4 * Real.arcsin (Real.sqrt p)) - 1 / 2)| ≤ 1 / 2 →
      (k : ℝ) ≤ Real.pi / (4 * Real.arcsin (Real.sqrt p)) ∧
      Real.pi / (4 * Real.arcsin (Real.sqrt p)) ≤ Real.pi / (4 * Real.sqrt p) ∧
      1 - p ≤ ‖inner ℂ ψ1 (act (ampAmpIterate A RG (0 : Qubits m) ^ k) (act A (zeroKet m)))‖ ^ 2 := by
  sorry

end QAlgorithms.DeWolf
