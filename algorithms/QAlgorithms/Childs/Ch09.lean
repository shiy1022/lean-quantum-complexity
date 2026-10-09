import QAlgorithms.Defs.Basic

/-!
# Childs, Chapter 9: Period finding from Z to R

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 9 (PDF pp. 45–49).

Conventions: the source's nearest-integer function `⌊x⌉` (§9.1, PDF p. 46) is Mathlib's `round`
(ties rounded up; the source never resolves ties, and its proof only uses that the rounding
error is at most `1/2` in absolute value). "`a/b` appears as a convergent in the continued
fraction expansion of `x`" is `∃ n, Real.convergent x n = a / b`; Mathlib's `Real.convergent`
coincides with the convergents of the regular continued fraction `GenContFract.of x`.
-/

namespace QAlgorithms.Childs

/-- Childs, Lemma 9.1 (PDF p. 48, proof p. 49): recovering an irrational period from two
Fourier samples. Let `r > 0` be a real period, let `j, j'` be relatively prime positive integers
below `r` (the multiples `⌊jN/r⌉, ⌊j'N/r⌉` returned by Fourier sampling over `Z_N`, §9.2,
PDF p. 48), and let `N ≥ 3r²`. Then `j/j'` appears as a convergent in the continued fraction
expansion of `⌊jN/r⌉/⌊j'N/r⌉`, and `|r − ⌊jN/⌊jN/r⌉⌉| ≤ 1`. -/
theorem periodFindingReals_convergent (r : ℝ) (N j j' : ℕ) (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (hjr : (j : ℝ) < r) (hj'r : (j' : ℝ) < r) (hcop : Nat.Coprime j j')
    (hN : 3 * r ^ 2 ≤ (N : ℝ)) :
    (∃ n : ℕ, Real.convergent
        ((round ((j : ℝ) * N / r) : ℝ) / (round ((j' : ℝ) * N / r) : ℝ)) n =
        ((j : ℚ) / (j' : ℚ))) ∧
      |r - (round ((j : ℝ) * N / (round ((j : ℝ) * N / r) : ℝ)) : ℝ)| ≤ 1 := by
  sorry

end QAlgorithms.Childs
