import QAlgorithms.Defs.Basic

/-!
# Childs, Chapter 8: Quantum algorithms for number fields

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 8 (PDF pp. 41–44): the units of
`Z[√d]` are the elements of norm `±1` (Proposition 8.1), and two principal ideals of `Z[√d]`
coincide iff their generators differ by a unit (Proposition 8.2).

Standing assumptions (§8.2, PDF p. 41; §8.3, PDF p. 42): `d` is a squarefree positive integer and
`√d` is irrational, which excludes `d = 1`; hence `Squarefree d` and `2 ≤ d`.
`Z[√d] = {x + y√d : x, y ∈ Z}` is Mathlib's `ℤ√d` (pairs `⟨x, y⟩` with
`(x + y√d)(w + z√d) = (xw + dyz) + (xz + yw)√d`); for non-square `d` it is isomorphic to the
subring of `ℝ` the source describes. Conjugation `x + y√d ↦ x − y√d` is `star`. A unit
(PDF p. 43: an element whose inverse over `Q(√d)` lies in `Z[√d]`) is `IsUnit` in `ℤ√d`, and the
principal ideal `ξ Z[√d]` is `Ideal.span {ξ}`.
-/

namespace QAlgorithms.Childs

/-- Childs, Proposition 8.1, PDF p. 43. Let `d` be a squarefree integer with `d ≥ 2`. Then
`ξ = x + y√d` is a unit in `Z[√d]` if and only if `ξ ξ̄ = x² − d y² = ±1`. -/
theorem zsqrtd_isUnit_iff (d : ℤ) (hd_sqfree : Squarefree d) (hd : 2 ≤ d) (x y : ℤ) :
    IsUnit (⟨x, y⟩ : ℤ√d) ↔ x ^ 2 - d * y ^ 2 = 1 ∨ x ^ 2 - d * y ^ 2 = -1 := by
  sorry

/-- Childs, Proposition 8.2, PDF p. 43. Let `d` be a squarefree integer with `d ≥ 2`. For
`ξ, ζ ∈ Z[√d]`, the principal ideals coincide, `ξ Z[√d] = ζ Z[√d]`, if and only if `ξ = ζ ϵ`
for some unit `ϵ` of `Z[√d]`. -/
theorem zsqrtd_span_singleton_eq_iff (d : ℤ) (hd_sqfree : Squarefree d) (hd : 2 ≤ d)
    (ξ ζ : ℤ√d) :
    Ideal.span {ξ} = Ideal.span {ζ} ↔ ∃ ϵ : ℤ√d, IsUnit ϵ ∧ ξ = ζ * ϵ := by
  sorry

end QAlgorithms.Childs
