import QAlgorithms.Defs.FieldCodeGeometry

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.BinaryCSS

/-- Logical-qubit dimension of a valid CSS pair; 0903.0566 p.4 (2). -/
def logicalDimension {I : Type*} [Fintype I]
    (CX CZ : Submodule (ZMod 2) (I → ZMod 2)) (_valid : codeDual CZ ≤ CX) : ℕ :=
  Module.finrank (ZMod 2) (CX ⧸ (codeDual CZ).comap CX.subtype)

/-- Exact CSS logical-error minimum; 0903.0566 p.4 (1), p.15, 2306.12470 p.5.
Empty logical-error sets have distance infinity. -/
def distance {I : Type*} [Fintype I]
    (CX CZ : Submodule (ZMod 2) (I → ZMod 2)) (_valid : codeDual CZ ≤ CX) : ℕ∞ :=
  min (⨅ x ∈ CX, ⨅ (_ : x ∉ codeDual CZ), (hammingNorm x : ℕ∞))
    (⨅ x ∈ CZ, ⨅ (_ : x ∉ codeDual CX), (hammingNorm x : ℕ∞))

example {I : Type*} [Fintype I]
    (C : Submodule (ZMod 2) (I → ZMod 2)) (h : codeDual C ≤ C) :
    distance C C h = ⨅ x ∈ C, ⨅ (_ : x ∉ codeDual C), (hammingNorm x : ℕ∞) := by
  simp [distance]

example : logicalDimension (⊥ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) ⊥
    (by intro x _; exact (Submodule.mem_bot _).mpr (Subsingleton.elim x 0)) = 0 := by
  unfold logicalDimension
  exact Module.finrank_zero_of_subsingleton
end QAlgorithms.BinaryCSS

