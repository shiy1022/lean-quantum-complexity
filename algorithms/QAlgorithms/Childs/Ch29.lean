import QAlgorithms.Defs.Hamiltonian

/-!
# Childs, Chapter 29: Quantum signal processing

A. Childs, *Lecture Notes on Quantum Algorithms*, §29.2 (PDF pp.152–153).

The signal rotation `W(x)` of (29.6) is `qspW x`, the rotation `e^{iϕσ_z}` is `qspZ ϕ`, and the
sequence `W_Φ(x) = e^{iϕ₀σ_z} W(x) e^{iϕ₁σ_z} ⋯ W(x) e^{iϕ_kσ_z}` of (29.7) is `qspSequence Φ x`
for `Φ : Fin (k + 1) → ℝ` (with `k` factors `W(x)`).
-/

namespace QAlgorithms.Childs

open Polynomial

/-- Childs, Lemma 29.1 (PDF p.152, citing [54, Theorem 3]): quantum signal processing.
For `k : ℕ` and `P, Q ∈ ℂ[x]`, there is `Φ ∈ ℝ^{k+1}` with
`W_Φ(x) = [[P(x), i Q(x) √(1−x²)], [i Q*(x) √(1−x²), P*(x)]]` for all `x ∈ [−1, 1]`
(the domain of `W(x)` in (29.6)) iff
(i) `deg P ≤ k` and `deg Q ≤ k − 1` (with `deg 0 = −∞`, so `Q = 0` when `k = 0`),
(ii) `P` has parity `k mod 2` and `Q` has parity `k − 1 ≡ k + 1 mod 2`, and
(iii) `|P(x)|² + (1 − x²)|Q(x)|² = 1` for all `x ∈ [−1, 1]`.
Here `P*` is `P` with conjugated coefficients. -/
theorem qsp_characterization (k : ℕ) (P Q : ℂ[X]) :
    (∃ Φ : Fin (k + 1) → ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      qspSequence Φ x =
        !![P.eval (x : ℂ), Complex.I * Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
          Complex.I * (Q.map (starRingEnd ℂ)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (P.map (starRingEnd ℂ)).eval (x : ℂ)]) ↔
    ((P.degree ≤ k ∧ Q.degree < k) ∧
      (HasParity P k ∧ HasParity Q (k + 1)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1) := by
  sorry

end QAlgorithms.Childs
