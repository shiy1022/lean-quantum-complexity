import QAlgorithms.Defs.GridSubgradientPrograms

noncomputable section

namespace QAlgorithms.Papers.RoadmapO14

open QAlgorithms.ValueAccess

/-! Chunk-local geometric access objects submitted in DEFINITION_REVIEW.md.
They assert no oracle success, local linearity, or curvature event. -/

/-- Finite regular query grid with compatible finite-difference radii.
Source: arXiv:1809.00643v4, pp.8-10, Lemma 18 and footnote 8, p.12. -/
structure SubgradientGrid (n : ℕ) where
  axisSize : ℕ
  axisSize_pos : 0 < axisSize
  mesh : ℝ
  origin : ℝ
  centerSpacing : ℝ
  centerTicks : ℕ
  differenceTicks : ℕ
  localBits : ℕ

/-- The query register stores the exact grid index, separately from its affine coordinates. -/
abbrev GridIndex {n : ℕ} (H : SubgradientGrid n) := Fin n → Fin H.axisSize

instance {n : ℕ} (H : SubgradientGrid n) : Nonempty (GridIndex H) :=
  ⟨fun _ => ⟨0, H.axisSize_pos⟩⟩

/-- Known affine coordinates of a finite binary-encoded grid index. -/
def queryPoint {n : ℕ} (H : SubgradientGrid n) (z : GridIndex H) : Fin n → ℝ :=
  fun i => H.origin + H.mesh * (z i : ℕ)

/-- Uniform center grid, at cell midpoints of the rounded inner cube. -/
def centerPoint {n : ℕ} (H : SubgradientGrid n)
    (z : Fin n → Fin (2 * H.centerTicks)) : Fin n → ℝ :=
  fun i => H.centerSpacing * ((z i : ℕ) + (1 / 2 : ℝ) - H.centerTicks)

/-- Geometric resolution and rounding conditions. The arithmetic guards preserve the
printed coefficient and near-linearity tolerance after rounding; they contain no f or U.
The precision threshold in the theorem is existential, not an attributed numeric bound. -/
def HasSubgradientGeometry {n : ℕ} (H : SubgradientGrid n)
    (r1 L delta rho precision : ℝ) : Prop :=
  let a : ℝ := H.centerSpacing * H.centerTicks
  let b : ℝ := H.centerSpacing * H.differenceTicks
  let r2 : ℝ := Real.sqrt (delta * r1 * rho / ((n : ℝ) * L))
  0 < H.mesh ∧ H.mesh ≤ precision ∧
  0 < H.centerSpacing ∧ H.centerSpacing ≤ precision ∧
  1 ≤ H.differenceTicks ∧ H.differenceTicks ≤ H.centerTicks ∧
  a ≤ r1 ∧ r1 - a ≤ precision ∧ b ≤ r2 ∧ r2 - b ≤ precision ∧
  (2 * b / n) * ((2 : ℝ) ^ H.localBits)⁻¹ ≤ precision ∧
  L * (2 * b / n) ≤ 28 * Real.pi * delta * (2 : ℝ) ^ H.localBits ∧
  (n : ℝ) * L * b ^ 2 / (rho * a) ≤ delta ∧
  (n : ℝ) * L * b / (rho * a) + 168 * Real.pi * delta * n / b ≤
    529 * Real.sqrt (delta * (n : ℝ) ^ 3 * L / (rho * r1)) ∧
  (∀ z : GridIndex H, ∀ i, |queryPoint H z i| ≤ 2 * r1) ∧
  (∃ index : (Fin n → Fin (2 * H.centerTicks)) → GridIndex H,
    ∀ z, queryPoint H (index z) = centerPoint H z) ∧
  (∃ index : (Fin n → Fin (2 * H.centerTicks)) →
      (Fin n → Qubits H.localBits) → GridIndex H,
    ∀ z u i, queryPoint H (index z u) i =
      centerPoint H z i + (2 * b / n) * gridPoint H.localBits (u i)) ∧
  (∃ index : (Fin n → Fin (2 * H.centerTicks)) → Fin n → Bool → GridIndex H,
    ∀ z j sign i, queryPoint H (index z j sign) i =
      centerPoint H z i + (if i = j then (if sign then b else -b) else 0))

/-- Standing assumptions of section 3: convex domain and objective, and Euclidean
Lipschitzness only on the closed outer cube. Its inclusion implies 0 is interior to C. -/
def IsLemma18Function {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (r1 L : ℝ) : Prop :=
  Convex ℝ C ∧ ConvexOn ℝ C f ∧
  {x : Fin n → ℝ | ∀ i, |x i| ≤ 2 * r1} ⊆ C ∧
  ∀ x y : Fin n → ℝ, (∀ i, |x i| ≤ 2 * r1) → (∀ i, |y i| ≤ 2 * r1) →
    |f x - f y| ≤ L * euclidNorm (x - y)

/-- Both printed inequalities, simultaneously for every y in C.
Lemma 18, arXiv:1809.00643v4, p.12. The omitted norm is Euclidean. -/
def SubgradientEvent {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (r1 L delta rho : ℝ) (g : Fin n → ℝ) : Prop :=
  ∀ y ∈ C,
    f 0 + g ⬝ᵥ y - 23 ^ 2 * Real.sqrt (delta * (n : ℝ) ^ 3 * L / (rho * r1)) *
      (∑ i, |y i|) - 2 * L * Real.sqrt n * r1 ≤ f y ∧
    f 0 + g ⬝ᵥ y - (23 * (n : ℝ)) ^ 2 * Real.sqrt (delta * L / (rho * r1)) *
      euclidNorm y - 2 * L * Real.sqrt n * r1 ≤ f y

/-- Lemma 18, arXiv:1809.00643v4, PDF p.12, proof p.13, including the relational
extension in footnote 7 (Definitions 2 and 28, pp.5 and 27).
Absolute asymptotic constants precede all instances. Resolution is geometric and can be
arbitrarily fine. Each actual procedure, normalized starts, workspace, input-independent
unitaries and decoder is fixed before C, f, the answer table and U. All uncontrolled U
and adjoint calls count; input is a value oracle. The conjuncts are the standard and
relational versions of this one headline result. -/
theorem convexSubgradient_quantum :
    ∃ K : ℝ, 0 < K ∧ ∃ scale0 : ℝ, 1 ≤ scale0 ∧
    ∀ n : ℕ, 1 ≤ n → ∀ r1 L delta rho : ℝ,
    0 < r1 → 0 < L → 0 < rho → rho ≤ 1 / 3 →
    0 < delta → delta ≤ r1 * n * L / rho →
    ∃ resolution : ℝ, 0 < resolution ∧
      (∀ precision : ℝ, 0 < precision → precision ≤ resolution →
        ∃ H : SubgradientGrid n, HasSubgradientGeometry H r1 L delta rho precision) ∧
      ∀ precision : ℝ, 0 < precision → precision ≤ resolution →
      ∀ H : SubgradientGrid n, HasSubgradientGeometry H r1 L delta rho precision →
        (∀ b : ℕ, ∀ encoding : FixedPointEncoding b,
          ∃ work : ℕ, ∃ P : RandomizedQueryProcedure n (GridIndex H × Qubits b) (Fin work),
            (scale0 ≤ (n : ℝ) / rho →
              procedureQueries P ≤ ⌈K * Real.log ((n : ℝ) / rho)⌉₊) ∧
            ∀ (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
              IsLemma18Function C f r1 L →
              ∀ U : Matrix (GridIndex H × Qubits b) (GridIndex H × Qubits b) ℂ,
                IsApproxBinaryValueOracle (queryPoint H) encoding.value false f delta U →
                queryProcedureLaw P U (SubgradientEvent C f r1 L delta rho) ≥ 1 - rho) ∧
        (∀ b w : ℕ, ∀ encoding : FixedPointEncoding b,
          ∃ work : ℕ,
          ∃ P : RandomizedQueryProcedure n (GridIndex H × (Qubits b × Qubits w)) (Fin work),
            (scale0 ≤ (n : ℝ) / rho →
              procedureQueries P ≤ ⌈K * Real.log ((n : ℝ) / rho)⌉₊) ∧
            ∀ (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
              IsLemma18Function C f r1 L →
              ∀ U : Matrix (GridIndex H × (Qubits b × Qubits w))
                  (GridIndex H × (Qubits b × Qubits w)) ℂ,
                IsRelationalValueApproximator (queryPoint H) encoding.value f delta U →
                queryProcedureLaw P U (SubgradientEvent C f r1 L delta rho) ≥ 1 - rho) := by sorry

end QAlgorithms.Papers.RoadmapO14
