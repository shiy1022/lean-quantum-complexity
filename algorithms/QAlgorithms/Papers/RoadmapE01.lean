import QAlgorithms.Defs.HypergraphProducts

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapE01

/-- Tillich--Zemor, arXiv:0903.0566v2, Theorem 1, PDF p.3.
The checks are the displayed construction on p.18 with both factors equal to H.
Quantum dimension counts logical qubits (p.4), while the coding space has
complex dimension 2^(k^2). Distance uses the explicit infinity convention
of p.15. The final implication gives the LDPC bound for any supplied uniform
row and column bounds, without imposing regularity on H. -/
theorem hypergraphProduct_parameters (r k : ℕ)
    (H : Matrix (Fin r) (Fin (r + k)) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H) :
    let N := (r + k) * (r + k) + r * r
    let e := HypergraphProduct.coordinateEquiv (r + k) (r + k) r r
    let HX : Matrix (Fin r × Fin (r + k)) (Fin N) (ZMod 2) :=
      (HypergraphProduct.checkVariable H H).submatrix id e.symm
    let HZ : Matrix (Fin (r + k) × Fin r) (Fin N) (ZMod 2) :=
      (HypergraphProduct.variableCheck H H).submatrix id e.symm
    let CX := FieldCodes.parityCheckCode HX
    let CZ := FieldCodes.parityCheckCode HZ
    let C := FieldCodes.parityCheckCode H
    Module.finrank (ZMod 2) C = k ∧
    HX * HZ.transpose = 0 ∧
    (∃ hCSS : codeDual CZ ≤ CX,
      BinaryCSS.logicalDimension CX CZ hCSS = k ^ 2 ∧
      Module.finrank ℂ (cssCode CX CZ) = 2 ^ (k ^ 2) ∧
      BinaryCSS.distance CX CZ hCSS = FieldCodes.minimumDistance C) ∧
    (∀ a : Fin r, ∀ b : Fin (r + k),
      hammingNorm (HX (a, b)) = hammingNorm (H a) + hammingNorm (fun i => H i b)) ∧
    (∀ b : Fin (r + k), ∀ a : Fin r,
      hammingNorm (HZ (b, a)) = hammingNorm (fun i => H i b) + hammingNorm (H a)) ∧
    (∀ rowBound colBound : ℕ,
      (∀ a, hammingNorm (H a) ≤ rowBound) →
      (∀ b, hammingNorm (fun i => H i b) ≤ colBound) →
      (∀ ab, hammingNorm (HX ab) ≤ rowBound + colBound) ∧
      (∀ ba, hammingNorm (HZ ba) ≤ rowBound + colBound)) := by sorry

end QAlgorithms.Papers.RoadmapE01