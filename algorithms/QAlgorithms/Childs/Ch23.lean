import QAlgorithms.Defs.Basic

/-!
# Childs, Chapter 23: the quantum adversary method

A. Childs, *Lecture Notes on Quantum Algorithms*, Chapter 23 (PDF pp. 117–120).
-/

namespace QAlgorithms.Childs

/-- Childs, Proposition 23.2 (PDF p. 118): for any `X ∈ ℂ^{m×n}`, `Y ∈ ℂ^{n×n}`,
`Z ∈ ℂ^{n×m}`, `|tr(XYZ)| ≤ ‖X‖_F ‖Y‖ ‖Z‖_F`, where `‖·‖_F` is the Frobenius norm
(`‖X‖_F² = ∑_{a,b} |X_ab|²`, p. 118) and `‖Y‖` the spectral (operator) norm (§1.3). -/
theorem trace_mul_mul_le_frob_spec_frob {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin m) ℂ) :
    ‖(X * Y * Z).trace‖ ≤ frobNorm X * specNorm Y * frobNorm Z := by
  sorry

end QAlgorithms.Childs
