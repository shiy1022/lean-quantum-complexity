import QAlgorithms.Defs.QECC

/-!
# Gottesman, *An introduction to quantum error correction*, §2.3–§3.1

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages): Theorem 5 (stabilizer
codes, p.10) and Lemma 1 (every syndrome occurs, p.12–13).
-/

namespace QAlgorithms.GottesmanIntro

open Stabilizer

/-- Gottesman intro p.10, Theorem 5: let `S` be an Abelian subgroup of order `2^a` of the
`n`-qubit Pauli group with `−1 ∉ S`, and let `d` be the minimum weight of a Pauli operator in
the normalizer `N(S)` (= the centralizer of `S` in `P_n`, p.10) that is not a phase times an
element of `S`. Then the stabilized space `T(S)` is an `[[n, n − a, d]]` code: it has dimension
`2^(n−a)`, every operator acting on at most `d − 1` qubits satisfies (34) on it, and some
operator acting on `d` qubits does not. The weight of a Pauli operator is the number of
non-identity tensor factors (p.4). The phases `±1, ±i` are removed from `N(S) \ S` since
otherwise `−I` (weight 0) would always lie in it. -/
theorem stabilizerCode_params (n a d : ℕ) (S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (hS : IsStabilizerGroup S) (hcard : Nat.card S = 2 ^ a)
    (hd : IsLeast {w : ℕ | ∃ Q ∈ pauliCentralizer S, Q ∉ phaseMultiples S ∧
      ∃ P : PauliString n, (Q : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix ∧ P.weight = w} d) :
    IsQCode n (n - a) d (stabilizedSpace S) ∧ HasDistance (stabilizedSpace S) d := by
  sorry

/-- Gottesman intro p.12–13, Lemma 1: given a stabilizer `S` (an Abelian subgroup of `P_n`
with `−1 ∉ S`) with independent generators `g_1, …, g_a` (so `|S| = 2^a`), every error syndrome
`v ∈ F_2^a` is the syndrome of some Pauli operator `E`: `E` commutes with `g_i` when `v_i = 0`
and anticommutes with `g_i` when `v_i = 1`. -/
theorem exists_pauli_of_syndrome (n a : ℕ) (g : Fin a → Matrix.unitaryGroup (Qubits n) ℂ)
    (hS : IsStabilizerGroup (Subgroup.closure (Set.range g)))
    (hcard : Nat.card (Subgroup.closure (Set.range g)) = 2 ^ a) (v : Fin a → ZMod 2) :
    ∃ E ∈ pauliGroup n, ∀ i : Fin a,
      (v i = 0 → (g i : Matrix (Qubits n) (Qubits n) ℂ) * E = E * g i) ∧
      (v i = 1 → (g i : Matrix (Qubits n) (Qubits n) ℂ) * E = -((E : Matrix (Qubits n) (Qubits n) ℂ) * g i)) := by
  sorry

end QAlgorithms.GottesmanIntro
