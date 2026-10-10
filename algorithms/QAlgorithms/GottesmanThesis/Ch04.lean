import QAlgorithms.Defs.BinaryStabilizer

/-!
# Gottesman, *Stabilizer codes and quantum error correction*, §4.1–§4.2

D. Gottesman, *Stabilizer codes and quantum error correction* (PhD thesis, 1997), cited
"Gottesman thesis p.N" (PDF pages): the standard form of a stabilizer (§4.1, p.39) and the
encoding network built from it (§4.2, pp.41–43, with the author's errata).

A code on `n = m + k` qubits encoding `k` qubits has `m = n − k` generators; its binary
generator matrix is `(H_x | H_z)` with `m` rows and `m + k` columns in each half.
-/

namespace QAlgorithms.GottesmanThesis

/-- Gottesman thesis p.39, §4.1 (unnumbered; equations (4.1)–(4.3)): every stabilizer code can
be put into the standard form (4.3). Let `(H_x | H_z)` be the binary generator matrix of `m`
independent commuting generators on `m + k` qubits (rows commute symplectically, eq. (3.23);
rows linearly independent over `F₂`). Then some sequence of generator replacements
`M_i ↦ M_i M_j` (row additions in both halves, i.e. left multiplication by an invertible
`G ∈ GL_m(F₂)`) and some rearrangement of the qubits (the same column permutation `σ` in both
halves) brings it to the standard form (4.3) with `r = rank H_x`: the first `r` rows read
`I A₁ A₂ | B C₁ C₂`, the last `m − r` rows read `0 0 0 | D I E`. -/
theorem standardForm_exists {m k : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hS : IsBinaryStabilizerMatrix Hx Hz) :
    ∃ G : Matrix.GeneralLinearGroup (Fin m) (ZMod 2), ∃ σ : Equiv.Perm (Fin (m + k)),
      IsStandardForm Hx.rank ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Hx.submatrix id σ)
        ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Hz.submatrix id σ) := by
  sorry

/-- Gottesman thesis pp.41–43, §4.2 (unnumbered; equation (4.8)), with the author's errata:
for a stabilizer in standard form (4.3) with rank parameter `r` and commuting rows, and the
logical `X̄` operators in the standard form of p.40 (`U₃ = I`, `V₃ = 0`, `U₂ = Eᵀ`,
`V₁ = EᵀC₁ᵀ + C₂ᵀ`), the encoding network of §4.2 maps the input `|0…0⟩|c₁…c_k⟩` (the first
`n − k` qubits in `|0⟩`, `|c_i⟩` in qubit `n − k + i`) to the normalized encoded basis state
`(I + M₁)⋯(I + M_{n−k}) X̄₁^{c₁}⋯X̄_k^{c_k} |0…0⟩`.

The network (`stabEncoder`) is the controlled-NOT step (each `X̄_i` without its last `σx`,
controlled on qubit `n − k + i`), followed, for `i = 1, …, r` in turn, by `R` on qubit `i`, `σz`
on qubit `i` if `B_ii = 1`, and `M_i` (without its qubit-`i` factor) controlled on qubit `i`
(erratum: Hadamard just before the qubit's control dots). Generators and `X̄`'s are the
real-form Pauli products `σz^b σx^a` with sign `+1` (errata: controlled-`Y` is controlled-`XZ`;
the method needs every generator of sign `+1`). -/
theorem stabEncoder_encodes {m k r : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hstd : IsStandardForm r Hx Hz) (hcomm : SymplecticCommuting Hx Hz) (c : Qubits k) :
    act (stabEncoder r Hx Hz).unitary (ket (Fin.append (fun _ : Fin m => false) c)) =
      normalizedVec (stabEncodedState r Hx Hz c) := by
  sorry

end QAlgorithms.GottesmanThesis
