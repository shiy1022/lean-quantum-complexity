import QAlgorithms.Defs.Walk

/-!
# Mixed states, measurements, encodings (shared definition layer)
-/

namespace QAlgorithms

open scoped ComplexConjugate ComplexOrder

/-- de Wolf p.139 (§15.1: "the set of density matrices is exactly the set of positive semidefinite
matrices of trace 1"): `ρ` is a density matrix. -/
def IsDensityMatrix {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- de Wolf p.140 (§15.1), p.141 (§15.2: "a measurement `{M_i, I − M_i}`"): `M` is the first
operator of a two-outcome POVM `{M, I − M}`: `0 ⪯ M ⪯ I`. -/
def IsEffect {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Prop :=
  M.PosSemidef ∧ (1 - M).PosSemidef

/-- de Wolf p.140 (§15.1): the probability `Tr(Mρ)` of the outcome with POVM operator `M` when
measuring `ρ` (a real number for an effect `M` and a density matrix `ρ`; its real part). -/
noncomputable def effectProb {ι : Type*} [Fintype ι] (M ρ : Matrix ι ι ℂ) : ℝ :=
  (M * ρ).trace.re

/-- de Wolf p.139 (§15.1): the density matrix `|ψ⟩⟨ψ|` of a pure state. -/
noncomputable def pureDensity {ι : Type*} (ψ : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun a b => ψ a * conj (ψ b)

/-- de Wolf p.170 (§18.1: "tracing out Alice's part of the space: `ρ_B = Tr_A(ρ_AB)`"), p.172:
the partial trace over the first tensor factor, `(Tr_A M)_{b b'} = Σ_a M_{(a,b),(a,b')}`. -/
def traceLeft {α β : Type*} [Fintype α] (M : Matrix (α × β) (α × β) ℂ) : Matrix β β ℂ :=
  Matrix.of fun b b' => ∑ a, M (a, b) (a, b')

/-- de Wolf p.142 (Theorem 4): the binary entropy in bits,
`H(p) = −p log₂ p − (1 − p) log₂(1 − p)` (Mathlib's `Real.binEntropy` is in nats; `0 log 0 = 0`). -/
noncomputable def binEntropy2 (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

/-- de Wolf p.141–142 (§15.2, Theorem 4): `x ↦ ρ_x` encodes `n`-bit strings into `m`-qubit states
such that, for each `i`, some two-outcome measurement `{M_i, I − M_i}` (`M_i` = output `1`)
recovers `x_i` with success probability at least `p` averaged over a uniformly random `x` (an
average, as Theorem 4 says, not a worst-case guarantee). -/
def IsQRAC {n m : ℕ} (ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ) (p : ℝ) : Prop :=
  (∀ x, IsDensityMatrix (ρ x)) ∧
    ∀ i : Fin n, ∃ M : Matrix (Qubits m) (Qubits m) ℂ, IsEffect M ∧
      ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool,
        (if x i then effectProb M (ρ x) else 1 - effectProb M (ρ x)) ≥ p

/-- de Wolf p.142 (Definition 3), p.143: `C : {0,1}ⁿ → {0,1}^N` is a `(q, δ, ε)`-locally decodable
code: a classical randomized decoder, which knows `i` (so one randomized decision tree per `i`)
and may query the `N`-bit string `y` adaptively at most `q` times, outputs `x_i` with probability
at least `1/2 + ε` for every `x`, every `i` and every `y` within Hamming distance `δN` of `C(x)`. -/
def IsLDC {n N : ℕ} (q : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)) : Prop :=
  ∀ i : Fin n, ∃ R : RandDecisionTree (Fin N) Bool Bool, RandMakesAtMost R q ∧
    ∀ (x : Fin n → Bool) (y : Fin N → Bool), (hammingDist (C x) y : ℝ) ≤ δ * N →
      successProb R y (x i) ≥ 1 / 2 + ε

/-! ### Sanity tests -/

/-- `Tr_A(C ⊗ D) = Tr(C) D`. -/
example {α β : Type*} [Fintype α] (C : Matrix α α ℂ) (D : Matrix β β ℂ) :
    traceLeft (Matrix.kronecker C D) = C.trace • D := by
  ext b b'
  simp [traceLeft, Matrix.kronecker, Matrix.trace, Finset.sum_mul]

/-- The binary entropy of a fair coin is one bit. -/
example : binEntropy2 (1 / 2) = 1 := by
  rw [binEntropy2, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- The identity is an effect (the measurement that always outputs `1`). -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] : IsEffect (1 : Matrix ι ι ℂ) := by
  refine ⟨Matrix.PosSemidef.one, ?_⟩
  rw [sub_self]
  exact Matrix.PosSemidef.zero

/-- A basis state gives a pure density matrix with a single `1` on the diagonal. -/
example {ι : Type*} [DecidableEq ι] (i : ι) : pureDensity (ket (ι := ι) i) i i = 1 := by
  simp [pureDensity, ket]

end QAlgorithms
