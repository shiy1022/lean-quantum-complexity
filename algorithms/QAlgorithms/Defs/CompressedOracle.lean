import QAlgorithms.Defs.Polynomial

/-!
# The compressed oracle (shared definition layer)

Childs §26: a random function `f : [n] → Σ`, `Σ = {0,1}^m` (here `Fin n → Qubits m`). The oracle
register holds one symbol of `Σ ∪ {⊥}` per input, modelled as `Option (Qubits m)` with
`none = ⊥`. The full register of an algorithm with the oracle register attached is indexed by
`((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))`, i.e. `|x, z, w, y⟩` as in (26.30).
-/

namespace QAlgorithms

/-- Childs p.133 (§26.1): `|ŷ⟩ = H^{⊗m}|y⟩`, as a vector of the oracle-register space
`span({|y⟩ : y ∈ Σ} ∪ {|⊥⟩})` (no `|⊥⟩` component). -/
noncomputable def hadKet (m : ℕ) (y : Qubits m) : EuclideanSpace ℂ (Option (Qubits m)) :=
  WithLp.toLp 2 fun o => match o with
    | none => 0
    | some z => hadamardN m z y

/-- Childs p.133 ((26.2)–(26.4)), p.137: the compression unitary
`C = I_Σ + |⊥⟩⟨0̂| + |0̂⟩⟨⊥| − |0̂⟩⟨0̂|`, i.e. `C|⊥⟩ = |0̂⟩`, `C|0̂⟩ = |⊥⟩`, `C|ŷ⟩ = |ŷ⟩` for
`y ≠ 0`, where `|0̂⟩ = 2^{−m/2} Σ_y |y⟩`. Entrywise: `C(⊥, ⊥) = 0`, `C(⊥, w) = C(z, ⊥) = 2^{−m/2}`,
`C(z, w) = δ_{zw} − 2^{−m}`. -/
noncomputable def compressionUnitary (m : ℕ) : Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ :=
  Matrix.of fun o o' => match o, o' with
    | none, none => 0
    | none, some _ => (((Real.sqrt 2)⁻¹ ^ m : ℝ) : ℂ)
    | some _, none => (((Real.sqrt 2)⁻¹ ^ m : ℝ) : ℂ)
    | some z, some w => (if z = w then 1 else 0) - ((((Real.sqrt 2)⁻¹ ^ m) ^ 2 : ℝ) : ℂ)

/-- Childs p.133: `C^{⊗n}`, the compression unitary on each of the `n` oracle registers. -/
noncomputable def compressAll (n m : ℕ) :
    Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ :=
  Matrix.of fun y y' => ∏ i : Fin n, compressionUnitary m (y i) (y' i)

/-- Childs p.133 ((26.1), extended as stated after (26.4)): the lookup unitary
`Λ |x⟩|z⟩|w⟩|y_1, …, y_n⟩ = |x⟩|z ⊕ y_x⟩|w⟩|y_1, …, y_n⟩` when `y_x ∈ Σ`, and the identity when
`y_x = ⊥`; the identity on the workspace `W`. -/
def lookupUnitary (n m : ℕ) (W : Type*) [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.of fun p q =>
    if p.1.1.1 = q.1.1.1 ∧ p.1.2 = q.1.2 ∧ p.2 = q.2 ∧
        p.1.1.2 = (match q.2 q.1.1.1 with
          | some v => q.1.1.2 + v
          | none => q.1.1.2)
    then 1 else 0

/-- Childs p.133 (§26.1): the compressed oracle `(I ⊗ I ⊗ C^{⊗n}) Λ (I ⊗ I ⊗ C^{⊗n})`, the
identity on the workspace. -/
noncomputable def compressedOracle (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.kronecker (1 : Matrix ((Fin n × Qubits m) × W) ((Fin n × Qubits m) × W) ℂ)
      (compressAll n m) * lookupUnitary n m W *
    Matrix.kronecker (1 : Matrix ((Fin n × Qubits m) × W) ((Fin n × Qubits m) × W) ℂ)
      (compressAll n m)

/-- Childs p.136 ((26.29)): the compressed phase oracle
`Φ = (I ⊗ H^{⊗m} ⊗ C^{⊗n}) Λ (I ⊗ H^{⊗m} ⊗ C^{⊗n})` (Hadamards on the output register `z`), the
identity on the workspace. -/
noncomputable def compressedPhaseOracle (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.kronecker (Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) (hadamardN m))
      (1 : Matrix W W ℂ)) (compressAll n m) * lookupUnitary n m W *
    Matrix.kronecker (Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) (hadamardN m))
      (1 : Matrix W W ℂ)) (compressAll n m)

/-- Childs p.136 (§26.3, `P`): the projection onto the basis states whose oracle register contains
a zero (`∃ x*, y_{x*} = 0^m`; `⊥` is not a zero). -/
def containsZeroProj (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.diagonal fun p => if ∃ x, p.2 x = some 0 then 1 else 0

/-- Childs p.133–134 (Lemma 26.1, `p`): the probability, over a uniformly random
`f : [n] → {0,1}^m` and the algorithm's measurement, that the algorithm `A` (standard queries
`|x⟩|z⟩ ↦ |x⟩|z ⊕ f(x)⟩`) outputs `k` pairs `(x_i, z_i) = out(outcome) i` that all lie in `R` and
satisfy `f(x_i) = z_i`. -/
noncomputable def randomOracleSuccess {n m k : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) (out : (Fin n × Qubits m) × W → (Fin k → Fin n × Qubits m))
    (R : Finset (Fin n × Qubits m)) : ℝ :=
  ((2 : ℝ) ^ (m * n))⁻¹ * ∑ f : Fin n → Qubits m,
    probEvent (A.finalState (xorOracle f)) fun z => ∀ i, out z i ∈ R ∧ f (out z i).1 = (out z i).2

/-- Childs p.133 (§26.1): the state of the algorithm `A` run with the compressed oracle: the same
unitaries `U_s ⊗ I` (identity on the oracle register), `compressedOracle` in place of each query,
from `|start⟩ ⊗ |⊥⟩^{⊗n}`; the state after `U_s`. -/
noncomputable def compressedStateAt {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) :
    Fin (t + 1) → EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) :=
  Fin.induction
    (act (Matrix.kronecker (A.U 0 : Matrix _ _ ℂ)
      (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ))
      (tensorVec A.start (ket fun _ => none)))
    (fun s ψ => act (Matrix.kronecker (A.U s.succ : Matrix _ _ ℂ)
      (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ))
      (act (compressedOracle n m W) ψ))

/-- The final state of `A` run with the compressed oracle. -/
noncomputable def compressedFinalState {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) :
    EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) :=
  compressedStateAt A (Fin.last t)

/-- Childs p.134 (Lemma 26.1, `p′`): run with the compressed oracle and measure all registers
(the oracle register included) in the computational basis; the probability that the output pairs
`(x_i, z_i)` all lie in `R` and the oracle register at `x_i` holds `z_i` (a `⊥` never matches). -/
noncomputable def compressedSuccess {n m k : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) (out : (Fin n × Qubits m) × W → (Fin k → Fin n × Qubits m))
    (R : Finset (Fin n × Qubits m)) : ℝ :=
  probEvent (compressedFinalState A) fun p =>
    ∀ i, out p.1 i ∈ R ∧ p.2 (out p.1 i).1 = some (out p.1 i).2

/-! ### Sanity tests -/

/-- For `m = 0` (`Σ` a single symbol, `|0̂⟩ = |0⟩`), `C` swaps `|⊥⟩` and `|0⟩`. -/
example : compressionUnitary 0 none none = 0 ∧ compressionUnitary 0 (some 0) none = 1 ∧
    compressionUnitary 0 (some 0) (some 0) = 0 := by
  simp [compressionUnitary]

/-- `C|⊥⟩ = |0̂⟩`: every entry of the `⊥` column on `Σ` is `2^{−m/2}`. -/
example (m : ℕ) (z : Qubits m) :
    compressionUnitary m (some z) none = (((Real.sqrt 2)⁻¹ ^ m : ℝ) : ℂ) := rfl

/-- `Λ` leaves a query to an unrecorded (`⊥`) position unchanged. -/
example (n m : ℕ) (W : Type*) [DecidableEq W] (x : Fin n) (z : Qubits m) (w : W)
    (y : Fin n → Option (Qubits m)) (hy : y x = none) :
    lookupUnitary n m W (((x, z), w), y) (((x, z), w), y) = 1 := by
  simp [lookupUnitary, hy]

/-- `Λ` adds the recorded value into the output register. -/
example (n m : ℕ) (W : Type*) [DecidableEq W] (x : Fin n) (z v : Qubits m) (w : W)
    (y : Fin n → Option (Qubits m)) (hy : y x = some v) :
    lookupUnitary n m W (((x, z + v), w), y) (((x, z), w), y) = 1 := by
  simp [lookupUnitary, hy]

end QAlgorithms
