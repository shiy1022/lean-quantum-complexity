# Pinned Mathlib API inventory (Q01)

Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, Lean 4.33.1. Every name marked
**available** is `#check`ed in [`src/Quantum/MathlibImports.lean`](../src/Quantum/MathlibImports.lean),
which compiles (local check, one Lean thread, 2026-10-05). Paths are relative to `Mathlib/`.
**Absent** means several spellings were searched in the pinned source and nothing was found. It
is a statement about this checkout, and it is the reason a qip task must build the item.

Status vocabulary: **available** (proved in Mathlib, compiled here) · **definition-only** ·
**absent** (to be built by the named task) · **project** (proved in this repository) ·
**external-pending** (RV01).

## Scopes and conventions to preserve

| Topic | Convention at this revision |
|---|---|
| Order on ℂ | `open scoped ComplexOrder` is required for `Matrix.PosSemidef` over ℂ |
| Loewner order | `open scoped MatrixOrder`; `Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef` (`Analysis/Matrix/Order.lean:58`). Required for `CFC.sqrt` on matrices |
| PSD definition | `Matrix.PosSemidef M := M.IsHermitian ∧ ∀ x : n →₀ R, 0 ≤ …` (finsupp form, `LinearAlgebra/Matrix/PosDef.lean:59`); use `posSemidef_iff_dotProduct_mulVec` for `star x ⬝ᵥ M *ᵥ x`. Positivity is never entrywise |
| Operator norm | No global matrix norm. `open scoped Matrix.Norms.L2Operator` gives the Euclidean operator norm (`Matrix.l2_opNorm_def`, `Analysis/CStarAlgebra/Matrix.lean:185`) and the C⋆-algebra structure. The `Pi` sup norm on raw coordinate vectors is **not** the Hilbert norm; use `EuclideanSpace ℂ n` |
| Inner product | `EuclideanSpace.inner_eq_star_dotProduct : ⟪x, y⟫ = ofLp y ⬝ᵥ star (ofLp x)`, conjugate-linear in the **first** argument (`Analysis/InnerProductSpace/PiL2.lean:215`) |
| `WithLp` | a structure (`toLp`/`ofLp`), not a type synonym; `Matrix.toEuclideanLin = toLpLin 2 2` |
| Kronecker | `open scoped Kronecker` for `⊗ₖ`; the left factor indexes the first component of `l × n`, matching `Quantum.Registers` |
| CP maps | `CompletelyPositiveMap A₁ A₂` is ℂ-linear between (non-unital) C⋆-algebras, with positivity tested on `CStarMatrix (Fin k) (Fin k) A₁`. For matrix algebras it needs the `L2Operator` C⋆ structure and `MatrixOrder`. Notation `→CP` needs `open scoped CStarAlgebra` |
| Spectral theorem | stated with `Unitary.conjStarAlgAut`, not `U * D * Uᴴ` |
| Square root | `CFC.sqrt` (a `cfcₙ NNReal.sqrt`); there is no `Matrix.PosSemidef.sqrt` at this revision |

## Inventory

| Area | Available (exact names) | Absent here → qip task |
|---|---|---|
| PSD / PosDef | `Matrix.PosSemidef`, `PosDef`, `posSemidef_iff_dotProduct_mulVec`, `PosSemidef.dotProduct_mulVec_nonneg`, `.submatrix`, `posSemidef_submatrix_equiv` (reindex form), `.conjTranspose_mul_mul_same`, `.mul_mul_conjTranspose_same`, `.trace_nonneg`, `.trace_eq_zero_iff`, `.eigenvalues_nonneg`, `.kronecker`, `posSemidef_conjTranspose_mul_self`, `posSemidef_self_mul_conjTranspose`, `posSemidef_iff_eq_sum_vecMulVec`, `isPositive_toEuclideanLin_iff` | matrix-specific `A = Bᴴ B` lemma (use `CStarAlgebra.nonneg_iff_eq_star_mul_self`, verified on matrices) → Q03 wrapper |
| Order | `Matrix.le_iff`, `nonneg_iff_posSemidef`, `PosSemidef.nonneg`, `instStarOrderedRing`, `tracePositiveLinearMap` | — |
| Spectrum | `IsHermitian.eigenvalues`, `eigenvectorBasis`, `eigenvectorUnitary`, `spectral_theorem`, `trace_eq_sum_eigenvalues` | — |
| Trace | `trace_mul_comm`, `trace_mul_cycle`, `trace_conjTranspose`, `trace_transpose`, `trace_kronecker` | `trace_submatrix`/`trace_reindex` for an equivalence → Q03 (one-line `Equiv.sum_comp`) |
| Norms | `toEuclideanCLM`, `l2_opNorm_def`, `cstar_norm_def`, `l2_opNorm_mulVec`, `l2_opNorm_conjTranspose_mul_self`, `toEuclideanLin`, `CStarMatrix` | — |
| CP / positive maps | `CompletelyPositiveMap`, `.map_cstarMatrix_nonneg`, `PositiveLinearMap.mk₀` | Choi matrix, Kraus form, Stinespring/dilation, quantum channel (CPTP) → Q06–Q08 |
| Tensor | `mul_kronecker_mul`, `kronecker_assoc`, `conjTranspose_kronecker`, `kronecker_mem_unitary` | **partial trace** (searched `partialTrace`, `traceLeft`, `traceRight`, `ptrace`) → Q05 |
| Unitaries | `mem_unitaryGroup_iff`, `kronecker_mem_unitary` | rectangular isometry predicate (`Vᴴ V = 1`, non-square) → Q08 |
| Compactness | `Metric.isCompact_of_isClosed_isBounded`, `FiniteDimensional.proper_rclike`, `IsCompact.exists_isMaxOn` | — |
| Separation | `geometric_hahn_banach_point_closed` and its real and `RCLike.` variants (`Analysis/LocallyConvex/Separation.lean`), `ProperCone.hyperplane_separation`, `.hyperplane_separation'`, `ProperCone.innerDual`, `.relative_hyperplane_separation` (Farkas) | SDP, conic duality, Slater (listed as a TODO in `Analysis/Convex/Cone/Basic.lean`) → Q22–Q23, built on the separation lemmas |
| Singular values | `LinearMap.singularValues`, `CFC.abs` | `Matrix.singularValues`, polar decomposition, trace norm, Schatten norms → Q10–Q11 |
| Functional calculus | `IsHermitian.cfc`, `IsHermitian.cfc_eq`, `CFC.sqrt`, `CFC.sqrt_nonneg`, `CFC.sqrt_mul_sqrt_self` (verified on `Matrix (Fin 2) (Fin 2) ℂ`) | — |
| Quantum notions | — | density operator, effect, fidelity, purification, Uhlmann → Q04, Q09–Q11 |

Deprecated at this revision (avoid): `Matrix.spectrum_toEuclideanLin` (use `spectrum_toLpLin`),
`Matrix.toEuclideanLin_toLp` (use `toLpLin_toLp`), `Matrix.isHermitian_iff_isSymmetric`,
`ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem` (use
`ProperCone.hyperplane_separation'`).

## Project theorems reused

None yet. qip currently imports only the **definitions** of
`Definitions/Def_ShiShallow_Core.lean` (sha256 recorded in `source-manifest.json`). Note that
every file under `bqp-pp/src/Theorems/` is a statement-only stub containing `sorry`. Q16 and
Q34 must reuse the proved top-level `BQP-*` / `AMPUNI-*` modules instead, after recording each
reused statement, source hash and transitive axiom report here.
