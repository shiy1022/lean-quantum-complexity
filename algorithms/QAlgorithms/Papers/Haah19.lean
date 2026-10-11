import QAlgorithms.Defs.LaurentQSP

/-!
# J. Haah, *Product decomposition of periodic functions in quantum signal processing*
(arXiv:1806.10236v4)

Cited "Haah p.N" (PDF pages). A Laurent polynomial `F(t) = Σ_j C_j t^j` with coefficients in
`Mat(2; ℂ)` is the frozen `LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)`, `C_j = F.coeff j`.
The classes `P_n`, `E_n` of Definition 1 (p.4, Eqs. (4)–(5)) are the frozen `IsQSPClassP`,
`IsQSPClassE`; "degree n" (`C_n ≠ 0` or `C_{−n} ≠ 0`) is `HasQSPDegree`; the primitive matrix
`E_P(t) = tP + t^{−1}(I − P)` of Eq. (2), `P` a rank-1 (orthogonal) projector, is
`primitiveMatrix P` with `IsRankOneProjector P`. The product `E_{P_1}(t) ⋯ E_{P_n}(t)` is the
left-to-right list product, factor `P_{j+1}` at index `j : Fin n`.
-/

namespace QAlgorithms.Papers.Haah19

open QAlgorithms
open scoped Matrix

/-- Haah Theorem 2 (p.4; proof pp.4–5). Write `E_P(t) = tP + t^{−1}(I − P)` for a rank-1
orthogonal projector `P` (Eq. (2), p.3).

1. For every `n` and rank-1 projectors `P_1, …, P_n`, the product `E_{P_1}(t) ⋯ E_{P_n}(t)`
   belongs to `E_n`.
2. Every `F(t) ∈ E_n` of degree `n` has a unique decomposition `F(t) = E_0 E_{P_1}(t) ⋯ E_{P_n}(t)`
   (Eq. (3)) with `E_0` independent of `t` and `P_1, …, P_n` rank-1 projectors; uniqueness is of
   the whole ordered tuple `(E_0, P_1, …, P_n)`, and the equality is of Laurent polynomials.
   The source's `E_0` is "a unitary"; since `det E_P(η) = 1` and `F(η) ∈ SU(2)` for `|η| = 1`,
   any unitary `E_0` in such a decomposition has determinant 1, so `E_0` ranges over `SU(2)`
   (= `P_0 = E_0`, p.4) without changing the statement.
3. If `n ≥ 1`, `F(t) = C_{−n}t^{−n} + ⋯ + C_n t^n`, then the last projector of the decomposition is
   `P_n = C_n† C_n / Tr(C_n† C_n)`. (That `C_n ≠ 0` is proved in the source, p.5, not assumed.) -/
theorem qsp_product_decomposition :
    (∀ (n : ℕ) (P : Fin n → Matrix (Fin 2) (Fin 2) ℂ), (∀ j, IsRankOneProjector (P j)) →
      IsQSPClassE n (List.ofFn fun j => primitiveMatrix (P j)).prod) ∧
    (∀ (n : ℕ) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)),
      IsQSPClassE n F → HasQSPDegree n F →
      ∃! D : Matrix.specialUnitaryGroup (Fin 2) ℂ × (Fin n → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j, IsRankOneProjector (D.2 j)) ∧
          F = LaurentPolynomial.C (D.1 : Matrix (Fin 2) (Fin 2) ℂ) *
            (List.ofFn fun j => primitiveMatrix (D.2 j)).prod) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)),
      IsQSPClassE n F → HasQSPDegree n F →
      ∀ (E0 : Matrix.specialUnitaryGroup (Fin 2) ℂ) (P : Fin n → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j, IsRankOneProjector (P j)) →
        F = LaurentPolynomial.C (E0 : Matrix (Fin 2) (Fin 2) ℂ) *
          (List.ofFn fun j => primitiveMatrix (P j)).prod →
        P ⟨n - 1, by omega⟩ =
          ((F.coeff (n : ℤ))ᴴ * F.coeff (n : ℤ)).trace⁻¹ • ((F.coeff (n : ℤ))ᴴ * F.coeff (n : ℤ))) := by
  sorry

end QAlgorithms.Papers.Haah19
