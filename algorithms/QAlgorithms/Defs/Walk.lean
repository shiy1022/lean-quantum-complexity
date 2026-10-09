import QAlgorithms.Defs.Hamiltonian

/-!
# Quantum walks and graph access (shared definition layer)

Childs's stochastic matrices are column-stochastic: `P_{kj}` is the probability of a transition
to `k` from `j` (p.90). Mathlib's `Matrix` stochasticity conventions are not used.
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- Childs p.90 (§18.2): `P` is stochastic in the source's sense: nonnegative entries and every
column sums to `1` (`P_{kj}` is the probability of a transition to `k` from `j`). -/
def IsColumnStochastic {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) : Prop :=
  (∀ j k, 0 ≤ P j k) ∧ ∀ j, ∑ k, P k j = 1

/-- Childs p.92 ((18.36)): `P_M`, the restriction of `P` to the unmarked vertices `V \ M`. -/
def unmarkedSubmatrix {ι : Type*} (P : Matrix ι ι ℝ) (M : Finset ι) :
    Matrix {v // v ∉ M} {v // v ∉ M} ℝ :=
  P.submatrix Subtype.val Subtype.val

/-- Childs p.90 ((18.5)–(18.6)): `|ψ_j⟩ = |j⟩ ⊗ Σ_k √(P_{kj}) |k⟩ = Σ_k √(P_{kj}) |j, k⟩` (the
square roots are of nonnegative entries for a stochastic `P`). -/
noncomputable def szegedyState {ι : Type*} [DecidableEq ι] (P : Matrix ι ι ℝ) (j : ι) :
    EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun p => if p.1 = j then (Real.sqrt (P p.2 j) : ℂ) else 0

/-- Childs p.90 ((18.7)): `Π = Σ_j |ψ_j⟩⟨ψ_j|`. -/
noncomputable def szegedyProj {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.of fun a b => ∑ j, szegedyState P j a * conj (szegedyState P j b)

/-- Childs p.90 ((18.8)): the swap `S = Σ_{j,k} |j, k⟩⟨k, j|`. -/
def swapOp {ι : Type*} [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.of fun a b => if a = (b.2, b.1) then 1 else 0

/-- Childs p.90 (§18.2): one step `U = S(2Π − 1)` of the quantum walk of `P`. -/
noncomputable def szegedyWalk {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  swapOp * (2 • szegedyProj P - 1)

/-- Childs p.91 (Theorem 18.1): the discriminant matrix `D_{jk} = √(P_{jk} P_{kj})`. -/
noncomputable def discriminant {ι : Type*} (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun j k => Real.sqrt (P j k * P k j)

/-- Childs p.143 (Lemma 27.1): `side` is a bipartition of `G` (every edge joins the two sides). -/
def IsBipartition {N : ℕ} (G : SimpleGraph (Fin N)) (side : Fin N → Bool) : Prop :=
  ∀ u v, G.Adj u v → side u ≠ side v

/-- Childs p.143 (§27.4, "we can efficiently compute the neighbors of any given vertex"):
`nbr v` lists the neighbours of `v` in `G`, each exactly once; `idx(α, β)` is the position of
`β` in `nbr α` (`List.idxOf`). -/
def IsNeighbourList {N : ℕ} (G : SimpleGraph (Fin N)) (nbr : Fin N → List (Fin N)) : Prop :=
  ∀ v, (nbr v).Nodup ∧ ∀ w, w ∈ nbr v ↔ G.Adj v w

/-- Childs p.143 (Lemma 27.1): `col` is a proper edge colouring of `G`: the colour of an edge does
not depend on its orientation, and two distinct edges at a common vertex get different colours. -/
def IsProperEdgeColouring {N : ℕ} {α : Type*} (G : SimpleGraph (Fin N)) (col : Fin N → Fin N → α) :
    Prop :=
  (∀ u v, G.Adj u v → col u v = col v u) ∧
    ∀ u v w, G.Adj u v → G.Adj u w → v ≠ w → col u v ≠ col u w

/-! ### Sanity tests -/

/-- The identity matrix (stay put) is column-stochastic. -/
example : IsColumnStochastic (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨fun j k => ?_, fun j => ?_⟩
  · by_cases h : j = k <;> simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply]

/-- `S` swaps the registers: `S|k, j⟩ = |j, k⟩`. -/
example (j k : Fin 2) : (swapOp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (j, k) (k, j) = 1 := by
  simp [swapOp]

/-- For the identity walk, the discriminant is the identity. -/
example : discriminant (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext j k
  by_cases h : j = k <;> simp [discriminant, Matrix.one_apply, h]

end QAlgorithms
