import QAlgorithms.Defs.BooleanFourier

/-!
# Learning models: exact, PAC and agnostic learning from classical or quantum data
(shared definition layer)

S. Arunachalam, R. de Wolf, *A survey of quantum learning theory* (2017), cited "survey p.N", and
S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), Chapters 6–7, cited
"Arunachalam p.N" (PDF pages).

Conventions:
* A concept is a Boolean function `c : X → Bool` on a finite domain `X` (`X = Qubits n` for the
  source's `{0,1}^n`; `true` is the label `1`), and a concept class is a `Finset (X → Bool)`.
* A distribution on a finite set is a real weight function (`IsDistribution`), so that the
  amplitudes `√D(x)` of quantum examples and the error probabilities are plain sums.
* A learner "using T examples" is modelled as one using exactly `T` (a learner using fewer can
  ignore the rest). A quantum learner is a POVM on `T` copies of the example state, one outcome per
  hypothesis; ancillas and internal randomness are absorbed into the POVM. A classical learner is
  a randomized map (a `PMF` over hypotheses) from the `T` labelled samples. The learner is fixed
  before the target concept and the distribution.
* Exact learners use membership queries: quantum ones the frozen `QueryAlg` with the XOR oracle
  `QMQ(c) = xorOracle c : |x, b⟩ ↦ |x, b ⊕ c(x)⟩`, classical ones randomized decision trees
  (`MQ(c)`; internal randomness is the distribution over trees).
-/

namespace QAlgorithms.Learning

open scoped ComplexConjugate ComplexOrder

open MeasureTheory

/-- Survey p.7 (§3.2, `D : {0,1}^n → [0,1]`), p.8 (§3.3, `D : {0,1}^{n+1} → [0,1]`), Arunachalam
p.127 (§6.3.2): a probability distribution on a finite set `X`, as a nonnegative real weight
function summing to `1`. -/
def IsDistribution {X : Type*} [Fintype X] (D : X → ℝ) : Prop :=
  (∀ x, 0 ≤ D x) ∧ ∑ x, D x = 1

/-- Arunachalam p.182 (§7.6.2, "drawn uniformly at random"): the uniform distribution
`D(x) = 1/|X|` on a finite set `X`. -/
noncomputable def uniformDist (X : Type*) [Fintype X] : X → ℝ :=
  fun _ => ((Fintype.card X : ℝ))⁻¹

/-- Survey p.7 (§3.2), Arunachalam p.127 (§6.3.2), p.169 (§7.6.1): the error of the hypothesis
`h` with respect to the target concept `c` under `D`, `err_D(h, c) = Pr_{x∼D}[h(x) ≠ c(x)]`. -/
noncomputable def pacError {X : Type*} [Fintype X] (D : X → ℝ) (c h : X → Bool) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => h x ≠ c x), D x

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): the error of `h` under a distribution `D` on
labelled pairs, `err_D(h) = Pr_{(x,b)∼D}[h(x) ≠ b]`. -/
noncomputable def agnosticError {X : Type*} [Fintype X] (D : X × Bool → ℝ) (h : X → Bool) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : X × Bool => h p.1 ≠ p.2), D p

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): `opt_D(C) = min_{c ∈ C} err_D(c)`, a minimum
over a finite set (so attained). Junk: `0` for an empty class; every statement using it has `C`
nonempty. -/
noncomputable def optError {X : Type*} [Fintype X] (D : X × Bool → ℝ) (C : Finset (X → Bool)) :
    ℝ :=
  ⨅ c : {c // c ∈ C}, agnosticError D c.1

/-- Survey p.12 (Def. 4.10), Arunachalam p.137 (Def. 6.5.1): the VC dimension of `C`, the size of
a largest `S ⊆ X` shattered by `C` (every labelling of `S` is realized by some `c ∈ C`). Computed
as Mathlib's `Finset.vcDim` of the family of supports `{x | c x = true}`: `S` is shattered by the
supports (`∀ t ⊆ S, ∃ c, S ∩ supp c = t`) iff every labelling of `S` is realized. Edge: an empty
class gets `0` (the source's value is undefined; statements fix the VC dimension `≥ 1`). -/
def vcDimClass {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) : ℕ :=
  (C.image fun c => Finset.univ.filter fun x => c x = true).vcDim

/-- Arunachalam p.163 (footnote 5): `C` is non-trivial, i.e. neither a single concept nor exactly
two complementary concepts `{c, 1 − c}` (and not empty). -/
def IsNontrivialClass {X : Type*} [DecidableEq X] [Fintype X] (C : Finset (X → Bool)) : Prop :=
  2 ≤ C.card ∧ ¬ ∃ c : X → Bool, C = {c, fun x => !c x}

/-- Survey p.7 (§3.2), Arunachalam p.127 (§6.3.2): the quantum example
`QPEX(c, D) = ∑_x √D(x) |x, c(x)⟩`, with real amplitudes (survey p.7, footnote 6). It is a unit
vector exactly when `∑ D = 1`. -/
noncomputable def exampleState {X : Type*} (c : X → Bool) (D : X → ℝ) :
    EuclideanSpace ℂ (X × Bool) :=
  WithLp.toLp 2 fun p => if p.2 = c p.1 then (Real.sqrt (D p.1) : ℂ) else 0

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): the quantum agnostic example
`QAEX(D) = ∑_{(x,b)} √D(x,b) |x, b⟩`. -/
noncomputable def agnosticExampleState {X : Type*} (D : X × Bool → ℝ) :
    EuclideanSpace ℂ (X × Bool) :=
  WithLp.toLp 2 fun p => (Real.sqrt (D p) : ℂ)

/-- Arunachalam p.158 (§7.1) and p.169 (§7.6.1): the `η`-noisy quantum example
`∑_x √((1−η)D(x)) |x, c(x)⟩ + √(ηD(x)) |x, 1 − c(x)⟩`. At `η = 0` it is `exampleState c D`. -/
noncomputable def noisyExampleState {X : Type*} (η : ℝ) (c : X → Bool) (D : X → ℝ) :
    EuclideanSpace ℂ (X × Bool) :=
  WithLp.toLp 2 fun p =>
    if p.2 = c p.1 then (Real.sqrt ((1 - η) * D p.1) : ℂ) else (Real.sqrt (η * D p.1) : ℂ)

/-- Survey p.7 (§3.2), Arunachalam p.128 (§6.3.2): `M` is an `(ε, δ)`-quantum PAC learner for
`C` using `T` quantum examples: a POVM on `T` copies of the quantum example, with one outcome per
hypothesis `h : X → Bool` (not required to lie in `C`), such that for every `c ∈ C` and every
distribution `D`, measuring `|ψ_{c,D}⟩^{⊗T}` yields an `h` with `err_D(h, c) ≤ ε` with probability
at least `1 − δ`. -/
def IsQPACLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (M : (X → Bool) → Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ) : Prop :=
  IsPOVM M ∧ ∀ c ∈ C, ∀ D : X → ℝ, IsDistribution D →
    povmEventProb M (pureDensity (tensorPow T (exampleState c D)))
      (fun h => pacError D c h ≤ ε) ≥ 1 - δ

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): `M` is an `(ε, δ)`-quantum agnostic learner
for `C` using `T` quantum examples: a POVM on `T` copies of `QAEX(D)` whose outcomes are the
concepts of `C` (the learner outputs `h ∈ C`), such that for every distribution `D` on
`X × {0,1}` the outcome `h` satisfies `err_D(h) ≤ opt_D(C) + ε` with probability at least
`1 − δ`. -/
def IsQAgnosticLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (M : {c // c ∈ C} → Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ) : Prop :=
  IsPOVM M ∧ ∀ D : X × Bool → ℝ, IsDistribution D →
    povmEventProb M (pureDensity (tensorPow T (agnosticExampleState D)))
      (fun h => agnosticError D h.1 ≤ optError D C + ε) ≥ 1 - δ

/-- Arunachalam p.169 (§7.6.1): `M` is an `(ε, δ)`-quantum PAC learner for `C` under random
classification noise of rate `η`, using `T` copies of the `η`-noisy quantum example: as
`IsQPACLearner`, with the noisy example state; success is still measured by the noiseless
`err_D(c, h) ≤ ε`. -/
def IsNoisyQPACLearner {X : Type*} [Fintype X] [DecidableEq X] (η : ℝ) (C : Finset (X → Bool))
    (ε δ : ℝ) (T : ℕ) (M : (X → Bool) → Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ) : Prop :=
  IsPOVM M ∧ ∀ c ∈ C, ∀ D : X → ℝ, IsDistribution D →
    povmEventProb M (pureDensity (tensorPow T (noisyExampleState η c D)))
      (fun h => pacError D c h ≤ ε) ≥ 1 - δ

/-- Survey p.6 (§3.2), Arunachalam p.127 (§6.3.2), p.152 (§7.1.1): `L` is a classical
`(ε, δ)`-PAC learner for `C` using `T` examples: a randomized map from `T` labelled examples to a
hypothesis `h : X → Bool` (not required to lie in `C`) such that, for every `c ∈ C` and every
distribution `D`, when the examples `(x_i, c(x_i))` have `x_1, …, x_T` i.i.d. from `D`, the
output satisfies `err_D(h, c) ≤ ε` with probability at least `1 − δ` (over the samples and the
learner's randomness). -/
def IsPACLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (L : (Fin T → X × Bool) → PMF (X → Bool)) : Prop :=
  ∀ c ∈ C, ∀ D : X → ℝ, IsDistribution D →
    ∑ xs : Fin T → X, (∏ i, D (xs i)) *
      ∑ h : X → Bool, (if pacError D c h ≤ ε then (L fun i => (xs i, c (xs i))) h else 0).toReal
      ≥ 1 - δ

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3), p.153 (§7.1.2): `L` is a classical
`(ε, δ)`-agnostic learner for `C` using `T` examples: a randomized map from `T` labelled samples
to a hypothesis in `C` such that, for every distribution `D` on `X × {0,1}` and `T` i.i.d.
samples from `D`, the output satisfies `err_D(h) ≤ opt_D(C) + ε` with probability at least
`1 − δ`. -/
def IsAgnosticLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (L : (Fin T → X × Bool) → PMF (X → Bool)) : Prop :=
  (∀ s, ∀ h ∈ (L s).support, h ∈ C) ∧
    ∀ D : X × Bool → ℝ, IsDistribution D →
      ∑ s : Fin T → X × Bool, (∏ i, D (s i)) *
        ∑ h : X → Bool, (if agnosticError D h ≤ optError D C + ε then L s h else 0).toReal
        ≥ 1 - δ

/-- Arunachalam p.166 (§7.4.3): `L` is a classical `ε`-average agnostic learner for `C` using `T`
samples: it outputs a hypothesis `h_{XY} : X → {0,1}` (the definition does not require
`h_{XY} ∈ C`, unlike the `(ε, δ)`-agnostic learner of p.117) and, for every distribution `D` on
`X × {0,1}`, `E_{(X,Y)∼D^T}[err_D(h_{XY})] − opt_D(C) ≤ ε` (the expectation also over the
learner's randomness). -/
def IsAvgAgnosticLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε : ℝ)
    (T : ℕ) (L : (Fin T → X × Bool) → PMF (X → Bool)) : Prop :=
  ∀ D : X × Bool → ℝ, IsDistribution D →
    (∑ s : Fin T → X × Bool, (∏ i, D (s i)) *
      ∑ h : X → Bool, (L s h).toReal * agnosticError D h) - optError D C ≤ ε

/-- Survey p.6 (§3.1), p.4 (§2.2), Arunachalam p.126 (§6.3.1): the `T`-query quantum algorithm
`A` (frozen `QueryAlg`: input-independent unitaries, fixed workspace `W`) with output map `out`
is a quantum exact learner for `C`: for every target `c ∈ C`, run with the membership oracle
`QMQ(c) : |x, b⟩ ↦ |x, b ⊕ c(x)⟩`, it outputs `h = c` with probability at least `2/3`
(footnote 4). -/
def IsQExactLearner {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (out : (ι × Bool) × W → (ι → Bool)) (C : Finset (ι → Bool)) :
    Prop :=
  ∀ c ∈ C, A.outputProb (xorOracle c) out c ≥ 2 / 3

/-- Survey p.6 (§3.1): the quantum query complexity `Q(C)` of exactly learning `C`, the least
`T` such that some `T`-query quantum exact learner for `C` exists (any finite workspace
`Fin w`). The set is nonempty (`|ι|` queries copying the truth table suffice), so the `sInf` is
the source's minimum. -/
noncomputable def quantumExactComplexity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset (ι → Bool)) : ℕ :=
  sInf {T : ℕ | ∃ (w : ℕ) (A : QueryAlg ι Bool (Fin w) T) (out : (ι × Bool) × Fin w → (ι → Bool)),
    IsQExactLearner A out C}

/-- Survey p.6 (§3.1): the classical query complexity `D(C)` of exactly learning `C` with
membership queries, the least `T` such that a randomized decision tree making at most `T` queries
outputs `c` with probability at least `2/3` for every target `c ∈ C`. The query bound is imposed
on every input, which changes nothing (cut each tree at depth `T`: the paths of the targets are
unaffected). The set is nonempty (query every index), so the `sInf` is the source's minimum. -/
noncomputable def classicalExactComplexity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset (ι → Bool)) : ℕ :=
  sInf {T : ℕ | ∃ R : RandDecisionTree ι Bool (ι → Bool), RandMakesAtMost R T ∧
    ∀ c ∈ C, successProb R c c ≥ 2 / 3}

/-- Survey p.6 (§3.1): the `(N, M)`-quantum query complexity of exact learning, `N = 2^n`, the
maximum of `Q(C)` over all classes `C ⊆ {0,1}^N` of size `M`. Junk `0` when `M > 2^N` (no such
class); statements carry `M ≤ 2^N`. -/
noncomputable def quantumExactNM (n M : ℕ) : ℕ :=
  ((Finset.univ : Finset (Qubits n → Bool)).powersetCard M).sup quantumExactComplexity

/-- Survey p.6 (§3.1): the classical `(N, M)`-query complexity of exact learning, `N = 2^n`, the
maximum of `D(C)` over all classes of size `M` (junk `0` when `M > 2^N`). -/
noncomputable def classicalExactNM (n M : ℕ) : ℕ :=
  ((Finset.univ : Finset (Qubits n → Bool)).powersetCard M).sup classicalExactComplexity

/-- Survey p.8 (Def. 4.1): `γ'(C', i, b) = |{c ∈ C' : c_i = b}| / |C'|`, the fraction of the
concepts in `C'` with `c_i = b`. Junk `0` at `C' = ∅`, never used (`γ` ranges over
`|C'| ≥ 2`). -/
noncomputable def gammaFrac {ι : Type*} (C' : Finset (ι → Bool)) (i : ι) (b : Bool) : ℝ :=
  ((C'.filter fun c => c i = b).card : ℝ) / (C'.card : ℝ)

/-- Survey p.8 (Def. 4.1): `γ'(C') = max_{i ∈ [N]} min{γ'(C', i, 0), γ'(C', i, 1)}`, a maximum
over the finite nonempty index set (`Qubits n` always has a point). -/
noncomputable def gammaPrime {ι : Type*} (C' : Finset (ι → Bool)) : ℝ :=
  ⨆ i : ι, min (gammaFrac C' i false) (gammaFrac C' i true)

/-- Survey p.8 (Def. 4.1): `γ(C) = min_{C' ⊆ C, |C'| ≥ 2} γ'(C')`, defined by the source for
`|C| > 1`; the minimum over a finite nonempty family. Lean's value for `|C| ≤ 1` is the junk `0`
(empty index), excluded by `2 ≤ C.card` in every statement. -/
noncomputable def gammaParam {ι : Type*} (C : Finset (ι → Bool)) : ℝ :=
  ⨅ C' : {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card}, gammaPrime C'.1

/-- Survey p.15 (§4.4): the set of two-outcome measurements on `n` qubits, given by the operator
`E` of the first outcome with `0 ≤ E ≤ I` (frozen `IsEffect`), with the subspace topology of the
matrices. -/
abbrev EffectSet (n : ℕ) := {E : Matrix (Qubits n) (Qubits n) ℂ // IsEffect E}

/-- Survey p.15 (§4.4): distributions `D` on the set of two-outcome measurements are Borel
probability measures for the subspace topology. -/
noncomputable instance (n : ℕ) : MeasurableSpace (EffectSet n) := borel (EffectSet n)

/-- The σ-algebra on `EffectSet n` is the Borel σ-algebra (survey p.15). -/
instance (n : ℕ) : BorelSpace (EffectSet n) := ⟨rfl⟩

/-- Survey p.15 (§4.4) and p.16 (Thm 4.16): the law of one measurement result `(E, b)`: `E` is
drawn from `D`, and given `E` the bit `b` is `1` with probability `Tr(Eρ)`. Written as the sum of
the two parts `b = 1` (density `Tr(Eρ)`) and `b = 0` (density `1 − Tr(Eρ)`), so that no kernel
measurability is involved. `T` i.i.d. results are `Measure.pi fun _ : Fin T => effectSampleLaw D ρ`.
-/
noncomputable def effectSampleLaw {n : ℕ} (D : Measure (EffectSet n))
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) : Measure (EffectSet n × Bool) :=
  (D.withDensity fun E => ENNReal.ofReal (effectProb E.1 ρ)).map (fun E => (E, true)) +
    (D.withDensity fun E => ENNReal.ofReal (1 - effectProb E.1 ρ)).map (fun E => (E, false))

/-! ### Sanity tests -/

example {X : Type*} [Fintype X] (D : X → ℝ) (c : X → Bool) : pacError D c c = 0 := by
  simp [pacError]

example {X : Type*} (c : X → Bool) (D : X → ℝ) : noisyExampleState 0 c D = exampleState c D := by
  ext p
  simp [noisyExampleState, exampleState]

theorem exampleState_norm {X : Type*} [Fintype X] {D : X → ℝ} (hD : IsDistribution D)
    (c : X → Bool) : ‖exampleState c D‖ = 1 := by
  have hsq : ‖exampleState c D‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    rw [← hD.2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_bool]
    cases h : c x <;>
      simp [exampleState, h, Complex.norm_real, Real.sq_sqrt (hD.1 x)]
  have h0 : 0 ≤ ‖exampleState c D‖ := norm_nonneg _
  nlinarith [hsq, h0]

example {X : Type*} [DecidableEq X] [Fintype X] (c : X → Bool) : ¬ IsNontrivialClass {c} := by
  simp [IsNontrivialClass]

example {ι : Type*} (i : ι) (b : Bool) : gammaFrac (∅ : Finset (ι → Bool)) i b = 0 := by
  simp [gammaFrac]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → Bool) :
    classicalExactComplexity {c} = 0 := by
  refine Nat.sInf_eq_zero.2 (Or.inl ⟨PMF.pure (DecisionTree.leaf c), ?_, ?_⟩)
  · intro t ht x
    rw [PMF.support_pure, Set.mem_singleton_iff] at ht
    subst ht
    rfl
  · intro c' hc'
    rw [Finset.mem_singleton] at hc'
    subst hc'
    simp [successProb, PMF.pure_map, DecisionTree.eval]
    norm_num

example {n : ℕ} (ρ : Matrix (Qubits n) (Qubits n) ℂ) : effectSampleLaw 0 ρ = 0 := by
  simp [effectSampleLaw]

end QAlgorithms.Learning
