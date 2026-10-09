import QAlgorithms.Defs.Search

/-!
# The generalized (negative-weights) adversary bound (shared definition layer)

Inputs are bit strings `x : ι → Bool` over a finite index type `ι` (the source's `[N]` or
`{1, …, n}`); a (possibly partial) Boolean function is `f : (ι → Bool) → Bool` together with
its domain `D : Finset (ι → Bool)`; only the values of `f` on `D` are ever read.
-/

namespace QAlgorithms

open scoped ComplexConjugate NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- de Wolf p.111 (§12.1), Childs p.118 (§23.2): `Γ` is an adversary matrix for `f` on `D`: a real
(possibly negative) symmetric `|D| × |D|` matrix with `Γ_{xy} = 0` whenever `f(x) = f(y)`. -/
def IsAdversaryMatrix (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) (Γ : Matrix D D ℝ) : Prop :=
  Γ.IsSymm ∧ ∀ x y : D, f x = f y → Γ x y = 0

/-- de Wolf p.112 (§12.1, Claim 2), Childs p.120 ((23.30)): `Γ_i`, obtained from `Γ` by setting
`Γ_{xy}` to `0` when `x_i = y_i`. -/
def maskMatrix {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) (i : ι) : Matrix D D ℝ :=
  Matrix.of fun x y => if (x : ι → Bool) i ≠ (y : ι → Bool) i then Γ x y else 0

/-- de Wolf p.112, Childs p.120: `max_i ‖Γ_i‖` (spectral norms). It is a supremum over the finite
type `ι`, hence a finite maximum; it is `0` when `ι` is empty (then `|D| ≤ 1` and every adversary
matrix is `0`). -/
noncomputable def maxMaskedNorm {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) : ℝ :=
  ⨆ i : ι, specNorm (maskMatrix Γ i)

/-- de Wolf p.111 (§12.1): the progress measure `S_t = Σ_{x,y ∈ D} Γ_{xy} α_x^* α_y ⟨ψ_x^t|ψ_y^t⟩`
of the algorithm `A` (standard queries to `x`) for the weights `α` (statements add
`Σ_x |α_x|² = 1`). -/
noncomputable def progressMeasure {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    {D : Finset (ι → Bool)} (A : QueryAlg ι Bool W T) (Γ : Matrix D D ℝ) (α : D → ℂ)
    (t : Fin (T + 1)) : ℂ :=
  ∑ x : D, ∑ y : D, (Γ x y : ℂ) * conj (α x) * α y *
    inner ℂ (A.stateAt (xorOracle (x : ι → Bool)) t) (A.stateAt (xorOracle (y : ι → Bool)) t)

/-- Childs p.123 ((24.1)): `Adv±(f) = max_Γ ‖Γ‖ / max_i ‖Γ_i‖` over the nonzero adversary matrices
of `f` on `D`. Taken in `ℝ≥0∞` so that the supremum is never a junk value (trap 5); it is `0`
when no nonzero adversary matrix exists (i.e. `f` constant on `D`), the convention for the
source's `0/0`. For `Γ ≠ 0` the denominator is positive (a nonzero `Γ_{xy}` has `x ≠ y`, hence
appears in some `Γ_i`). A total function is the case `D = Finset.univ`. -/
noncomputable def advPm (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) : ℝ≥0∞ :=
  ⨆ (Γ : Matrix D D ℝ) (_ : IsAdversaryMatrix f D Γ ∧ Γ ≠ 0),
    ENNReal.ofReal (specNorm Γ / maxMaskedNorm Γ)

/-- Childs p.124 (§24.1, (24.3)): the vectors `|v_{x,i}⟩ ∈ ℂ^d` (`x ∈ D`, `i ∈ ι`) are feasible for
the adversary dual: `Σ_{i : x_i ≠ y_i} ⟨v_{x,i}|v_{y,i}⟩ = 1 − δ_{f(x), f(y)}` for all `x ≠ y`. -/
def DualFeasibleChilds (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) (d : ℕ)
    (v : D → ι → EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ x y : D, x ≠ y →
    ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
      inner ℂ (v x i) (v y i) = if f x = f y then 0 else 1

/-- Childs p.124: the `b`-complexity `C_b = max_{x ∈ f^{−1}(b)} Σ_i ‖v_{x,i}‖²` (a maximum over a
finite set, `0` if `f` takes no value `b` on `D`). -/
noncomputable def childsBComplexity (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) {d : ℕ}
    (v : D → ι → EuclideanSpace ℂ (Fin d)) (b : Bool) : ℝ≥0 :=
  (Finset.univ.filter fun x : D => f x = b).sup fun x => ∑ i, ‖v x i‖₊ ^ 2

/-- Childs p.124 ((24.2)): the dual objective `max{C_0, C_1}`. -/
noncomputable def childsDualObjective (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) {d : ℕ}
    (v : D → ι → EuclideanSpace ℂ (Fin d)) : ℝ≥0 :=
  max (childsBComplexity f D v false) (childsBComplexity f D v true)

/-- de Wolf p.113 (§12.2): the vectors `u_{xj}, v_{xj} ∈ ℂ^d` are feasible for de Wolf's dual SDP:
`Σ_{j : x_j ≠ y_j} ⟨u_{xj}|v_{yj}⟩ = [f(x) ≠ f(y)]` for all `x, y ∈ D`. -/
def DualFeasibleDeWolf (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) (d : ℕ)
    (u v : D → ι → EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ x y : D,
    ∑ j ∈ Finset.univ.filter (fun j => (x : ι → Bool) j ≠ (y : ι → Bool) j),
      inner ℂ (u x j) (v y j) = if f x ≠ f y then 1 else 0

/-- de Wolf p.113 (§12.2): the dual objective `max_{x ∈ D} max(Σ_j ‖u_{xj}‖², Σ_j ‖v_{xj}‖²)`. -/
noncomputable def dewolfDualObjective {D : Finset (ι → Bool)} {d : ℕ}
    (u v : D → ι → EuclideanSpace ℂ (Fin d)) : ℝ≥0 :=
  Finset.univ.sup fun x : D => max (∑ j, ‖u x j‖₊ ^ 2) (∑ j, ‖v x j‖₊ ^ 2)

/-- Childs p.126 (§24.5): the composition `f ∘ g`, `(f ∘ g)(y) = f(g(y¹), …, g(yⁿ))`, where block
`i` of the input is `yⁱ = (y(i, j))_j` (the source's `n` consecutive blocks of `m` bits, up to the
relabelling `finProdFinEquiv`, under which `Adv±` is invariant). -/
def blockCompose {κ : Type*} (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool) :
    (ι × κ → Bool) → Bool :=
  fun y => f fun i => g fun j => y (i, j)

/-- Childs p.128 (§24.6, `U := (2Π − I)(2∆ − I)`), de Wolf p.114–115 (§12.3,
`U_x = (2Π_x − I)(2Λ − I)`): the product of the reflections through `K` and through `L` (the
reflection through `L` is applied first), on a finite-dimensional complex inner-product space. -/
noncomputable def reflProduct {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (K L : Submodule ℂ E) : E →L[ℂ] E :=
  K.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
    L.reflection.toContinuousLinearEquiv.toContinuousLinearMap

/-- Childs p.128 (Lemma 24.3: "`P_ω` the projector onto eigenvectors of `U` with eigenvalues `e^{iθ}`
with `|θ| < ω`"), de Wolf p.115 (§12.3: `P_Θ = Σ_{β : |θ_β| ≤ Θ} |β⟩⟨β|`): the orthogonal
projection onto the span of the eigenvectors of `U` whose eigenvalue lies in `S`. For a unitary
`U` (orthogonal eigenspaces) this is `Σ_{β : λ_β ∈ S} |β⟩⟨β|` for any orthonormal eigenbasis.
Childs's `P_ω` is `S = {λ | |arg λ| < ω}`, de Wolf's `P_Θ` is `S = {λ | |arg λ| ≤ Θ}`; `Complex.arg`
takes values in `(−π, π]`, the sources' range for `θ`. -/
noncomputable def eigenProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E →L[ℂ] E) (S : Set ℂ) : E →L[ℂ] E :=
  (⨆ μ ∈ S, Module.End.eigenspace (U : E →ₗ[ℂ] E) μ).starProjection

/-! ### The objects of de Wolf §12.3 -/

/-- de Wolf p.114 (§12.3): the state space of the algorithm: a first register with basis `|0⟩` and
`|j⟩`, `j ∈ [N]` (input position `j : Fin N` is index `j.succ`), one qubit, and a third register
with basis `|0⟩, |1⟩, …, |d⟩` (a vector `w ∈ ℂ^d` sits on the indices `1, …, d`). -/
abbrev AdvSpace (N d : ℕ) := EuclideanSpace ℂ (Fin (N + 1) × (Bool × Fin (d + 1)))

/-- de Wolf p.114 (§12.3): the data of the algorithm: a function `f` on the domain `D ⊆ {0,1}^N`
and vectors `u_{xj}, v_{xj} ∈ ℂ^d` (a solution of the dual SDP, whose feasibility
`DualFeasibleDeWolf` is a hypothesis of the statements). -/
structure AdvAlg (N : ℕ) where
  /-- The domain of the partial function. -/
  D : Finset (Fin N → Bool)
  /-- The function (only its values on `D` matter). -/
  f : (Fin N → Bool) → Bool
  /-- The dimension of the dual vectors. -/
  d : ℕ
  /-- The vectors `u_{xj}`. -/
  u : D → Fin N → EuclideanSpace ℂ (Fin d)
  /-- The vectors `v_{xj}`. -/
  v : D → Fin N → EuclideanSpace ℂ (Fin d)

namespace AdvAlg

variable {N : ℕ} (P : AdvAlg N)

/-- de Wolf p.114: `A`, the objective value of the dual solution. -/
noncomputable def A : ℝ :=
  (dewolfDualObjective P.u P.v : ℝ)

/-- A vector of `ℂ^d` placed on the basis states `|1⟩, …, |d⟩` of the third register. -/
noncomputable def thirdReg (w : EuclideanSpace ℂ (Fin P.d)) : EuclideanSpace ℂ (Fin (P.d + 1)) :=
  WithLp.toLp 2 (Fin.cons 0 fun k => w k)

/-- de Wolf p.114: `|t^+_x⟩ = (|0⟩|0⟩|0⟩ + |1⟩|f(x)⟩|0⟩)/√2`, with `|1⟩` the first-register basis
state of index `1` (copied literally; it needs `N ≥ 1`, for `N = 0` the index `1` wraps to `0`). -/
noncomputable def tPlus (x : Fin N → Bool) : AdvSpace N P.d :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket ((0 : Fin (N + 1)), (false, (0 : Fin (P.d + 1)))) +
    ket ((1 : Fin (N + 1)), (P.f x, (0 : Fin (P.d + 1)))))

/-- de Wolf p.114: `|t^−_x⟩ = (|0⟩|0⟩|0⟩ − |1⟩|f(x)⟩|0⟩)/√2`. -/
noncomputable def tMinus (x : Fin N → Bool) : AdvSpace N P.d :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket ((0 : Fin (N + 1)), (false, (0 : Fin (P.d + 1)))) -
    ket ((1 : Fin (N + 1)), (P.f x, (0 : Fin (P.d + 1)))))

/-- de Wolf p.114: the (unnormalized) state `|ψ_y⟩ = (0.01/√A) |t^−_y⟩ − Σ_j |j⟩|ȳ_j⟩|v_{yj}⟩`,
`ȳ_j = 1 − y_j`. (Statements assume `A ≥ 1`, as the source does, so `√A > 0`.) -/
noncomputable def psi (y : P.D) : AdvSpace N P.d :=
  ((0.01 / Real.sqrt P.A : ℝ) : ℂ) • P.tMinus y -
    ∑ j : Fin N, tensorVec (ket j.succ) (tensorVec (ket (!(y : Fin N → Bool) j)) (P.thirdReg (P.v y j)))

/-- de Wolf p.114–115: the subspace of `Λ`, orthogonal to the span of the `|ψ_y⟩`, `y ∈ D`. -/
noncomputable def lambdaSpace : Submodule ℂ (AdvSpace N P.d) :=
  (Submodule.span ℂ (Set.range P.psi))ᗮ

/-- de Wolf p.115: the subspace of `Π_x`, spanned by the states with `|j⟩|x_j⟩` in the first two
registers (`j ∈ [N]`, any third register) and the states with `|0⟩` in the third register. -/
noncomputable def piSpace (x : Fin N → Bool) : Submodule ℂ (AdvSpace N P.d) :=
  Submodule.span ℂ (ket '' {z : Fin (N + 1) × (Bool × Fin (P.d + 1)) |
    (∃ j : Fin N, z.1 = j.succ ∧ z.2.1 = x j) ∨ z.2.2 = 0})

/-- de Wolf p.114: `U_x = (2Π_x − I)(2Λ − I)`. -/
noncomputable def walk (x : Fin N → Bool) : AdvSpace N P.d →L[ℂ] AdvSpace N P.d :=
  reflProduct (P.piSpace x) P.lambdaSpace

end AdvAlg

/-! ### Sanity tests -/

/-- The zero matrix is an adversary matrix for every function. -/
example (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) : IsAdversaryMatrix f D 0 :=
  ⟨Matrix.isSymm_zero, fun _ _ _ => rfl⟩

/-- `Γ_i` keeps exactly the entries where `x_i ≠ y_i`. -/
example {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) (i : ι) (x : D) : maskMatrix Γ i x x = 0 := by
  simp [maskMatrix]

/-- A constant function has no nonzero adversary matrix, so `Adv± = 0`. -/
example (D : Finset (ι → Bool)) : advPm (fun _ => true) D = 0 := by
  refine le_antisymm (iSup₂_le fun Γ hΓ => ?_) bot_le
  exfalso
  exact hΓ.2 (Matrix.ext fun x y => hΓ.1.2 x y rfl)

/-- A reflection is an involution, so `(2Π_K − I)(2Π_K − I) = I`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (K : Submodule ℂ E) (v : E) : reflProduct K K v = v := by
  simp [reflProduct, Submodule.reflection_reflection]

/-- The reflection through the whole space is the identity: `2Π − I = I` for `Π = I`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (v : E) : (⊤ : Submodule ℂ E).reflection v = v := by
  simp [Submodule.reflection_apply, Submodule.starProjection_top, two_smul]

/-- de Wolf p.116 (§12.4): composing with the identity on one block gives `f` back. -/
example (f : (ι → Bool) → Bool) (y : ι × Unit → Bool) :
    blockCompose f (fun z : Unit → Bool => z ()) y = f fun i => y (i, ()) := rfl

end QAlgorithms
