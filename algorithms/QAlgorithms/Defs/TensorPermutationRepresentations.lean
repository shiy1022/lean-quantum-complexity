import QAlgorithms.Defs.SchurShapes

noncomputable section

namespace QAlgorithms.Schur

/-- Tensor-factor permutation action |j> ↦ |j ∘ pi^{-1}>; this is computed from the
permutation, rather than an arbitrary representation (1508.01797 p.4, §III). -/
def tensorPermutation (d n : ℕ) (pi : Equiv.Perm (Fin n)) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun y x => if y = x ∘ pi.symm then 1 else 0

example (d n : ℕ) : tensorPermutation d n 1 = 1 := by
  ext y x
  rfl

example (x : Fin 2 → Fin 2) :
    tensorPermutation 2 2 (Equiv.swap 0 1) (x ∘ Equiv.swap 0 1) x = 1 := by
  simp [tensorPermutation]

end QAlgorithms.Schur
