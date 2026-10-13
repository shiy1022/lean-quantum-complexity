import QAlgorithms.Defs.WeightedDQI
import QAlgorithms.Defs.DQI

noncomputable section

open Filter

namespace QAlgorithms.Papers.RoadmapD03

open QAlgorithms.WeightedDQI

/-- The admissible data of Theorem 2, arXiv:2605.10666v2, PDF pp.5–6.
The range `1 ≤ r < p` is recovered from Appendix A, PDF p.30. The degree ratio
is exact; no rounded degrees are substituted for irrational ratios.
The dual-distance condition has the source's strict `2*l + 1 < d^perp` strength. -/
structure WeightedInstance (kappa mu : ℝ) where
  clauses : ClauseDomain
  m : ℕ
  n : ℕ
  blocks : ℕ
  ell : ℕ
  m_pos : 0 < m
  B : Matrix (Fin m) (Fin n) (ZMod clauses.p)
  L : Fin m → Finset (ZMod clauses.p)
  cardinality : ∀ i, (L i).card = clauses.r
  partition : BlockPartition m blocks
  distance : DualDistanceExceeds B (2 * ell + 1)
  kappa_eq : clauseParameters clauses 2 = kappa
  ratio_eq : (ell : ℝ) / m = mu

/-- The optimal signed expectation in (9), PDF p.6: the supremum over unit
multivariate DQI states of total degree at most `ell`. Attainment is a conclusion
of the headline, rather than an assumption on the data. -/
def weightedOptimalValue {kappa mu : ℝ} (I : WeightedInstance kappa mu) : ℝ :=
  letI : NeZero I.clauses.p := ⟨I.clauses.prime.ne_zero⟩
  optimalExpectation I.B I.L I.partition I.ell

/-- The actual Born-rule expectation of the polynomial state, (8), PDF pp.5–6.
Its unit norm is required by the admissibility clauses in the headline. -/
def polynomialExpectation {kappa mu : ℝ} (I : WeightedInstance kappa mu)
    (P : MvPolynomial (Fin I.blocks) ℂ) : ℝ :=
  letI : NeZero I.clauses.p := ⟨I.clauses.prime.ne_zero⟩
  ∑ x, prob (state I.B I.L I.partition P) x * objective I.B I.L I.partition x

/-- The signed remainder of equation (9), PDF p.6. The frozen variationalValue
is precisely Gamma in (10), including the slack budget and allocation endpoints. -/
def residual {kappa mu : ℝ} (I : WeightedInstance kappa mu) : ℝ :=
  weightedOptimalValue I / I.m -
    clauseParameters I.clauses 0 *
      ((I.m : ℝ)⁻¹ * ∑ t, I.partition.weights t * (I.partition.blocks t).card) -
    clauseParameters I.clauses 1 *
      variationalValue I.partition I.m_pos kappa mu (by
        rw [← I.ratio_eq]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The nonnegative error scale in (9), PDF p.6; the fractional power is real. -/
def errorScale {kappa mu : ℝ} (I : WeightedInstance kappa mu) : ℝ :=
  (I.m : ℝ)⁻¹ * ∑ t, I.partition.weights t *
    ((I.partition.blocks t).card : ℝ) ^ (3 / 4 : ℝ)

/-- Theorem 2 (Asymptotically Optimal Expectation Value), arXiv:2605.10666v2,
PDF p.6, equations (9)–(10), proved in Appendix A, PDF pp.30–38.
The printed theorem omits the clause-size range; `ClauseDomain` carries
`1 ≤ r < p` explicitly declared on p.30. No formula is changed.
The constants depend only on kappa and precede all uniform instance data.
The final clause is convergence of the remainder, with fixed block count and
eventually bounded weights, and does not require limiting block proportions. -/
theorem weightedDQI_optimalExpectation :
    ∀ kappa : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ m0 : ℕ,
      (∀ mu : ℝ, 0 < mu → mu < 1 / 2 → ∀ I : WeightedInstance kappa mu,
        (letI : NeZero I.clauses.p := ⟨I.clauses.prime.ne_zero⟩
          ∃ P : MvPolynomial (Fin I.blocks) ℂ,
            P.totalDegree ≤ I.ell ∧ IsState (state I.B I.L I.partition P) ∧
            polynomialExpectation I P = weightedOptimalValue I) ∧
        (m0 ≤ I.m → |residual I| ≤ C * errorScale I)) ∧
      (∀ (N : ℕ) (mu : ℝ), 0 < mu → mu < 1 / 2 →
        ∀ family : ℕ → WeightedInstance kappa mu,
          (∀ j, (family j).blocks = N) →
          Tendsto (fun j => (family j).m) atTop atTop →
          (∃ G : ℝ, 0 < G ∧ ∀ᶠ j in atTop,
            ∀ t, (family j).partition.weights t ≤ G) →
          Tendsto (fun j => residual (family j)) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.RoadmapD03