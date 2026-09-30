import «AMPUNI-layout-data»

set_option autoImplicit false

namespace ShiTMLayoutMachine

/-- Unary piece tables use only marks and delimiters, never the mirror sentinel. -/
theorem pieceCells_ne_mirrorEnd (f : Nat × Nat → Nat)
    (ps : List (Nat × Nat)) :
    ∀ y ∈ pieceCells f ps, y ≠ Cell.mirrorEnd := by
  induction ps with
  | nil => simp [pieceCells]
  | cons p ps ih =>
      intro y hy
      simp [pieceCells] at hy
      rcases hy with ⟨_, rfl⟩ | rfl | hy
      · simp
      · simp
      · exact ih y hy

end ShiTMLayoutMachine
