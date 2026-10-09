import QAlgorithms.Defs.Query

/-!
# Quantum Fourier transform, phase estimation, period finding, Abelian HSP
(shared definition layer)

Conventions: `ω_N = e^{2πi/N}` with sign `+` and normalization `1/√N` (de Wolf p.41; trap Q9);
the qubit QFT uses the most-significant-bit-first index map `bitsEquivFin`.
-/

namespace QAlgorithms

/-- de Wolf p.41 (§4.1): the Fourier matrix `F_N`, whose `(j, k)` entry is
`ω_N^{jk} / √N = e^{2πi jk/N} / √N` (rows and columns indexed by `0, …, N − 1`). Its inverse is the
conjugate transpose `star (qftMatrix N)` (entries `ω_N^{−jk}/√N`, p.42). -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) * (k : ℕ) : ℕ) : ℂ) / (N : ℂ)) /
      (Real.sqrt N : ℂ)

/-- de Wolf p.43 (§4.4), p.44 (§4.5): the `n`-qubit quantum Fourier transform `F_{2ⁿ}`, with
`|k⟩ = |k₁ … kₙ⟩`, `k₁` the most significant bit (the index map `bitsEquivFin`). -/
noncomputable def qftQubits (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  (qftMatrix (2 ^ n)).submatrix (bitsEquivFin n) (bitsEquivFin n)

/-- de Wolf p.44–45 (§4.5): the elementary gates allowed for the QFT circuit: Hadamards,
controlled-`R_s` gates (`s ≥ 1`; `R_1 = Z`, as the source notes), and the swap gates used at the
end of the circuit. -/
def qftGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard} ∪ {g | ∃ s : ℕ, 1 ≤ s ∧ g = Gate.ofMatrix2 (controlled (rotR s))} ∪
    {Gate.ofMatrix2 swapGate}

/-- de Wolf p.46 (§4.6, step 3): the map `|j⟩|ψ⟩ ↦ |j⟩ U^j |ψ⟩` (apply `U` to the second register
`j` times, `j` read most significant bit first), i.e. `Σ_j |j⟩⟨j| ⊗ U^j`. -/
def controlledPower {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ) (U : Matrix κ κ ℂ) :
    Matrix (Qubits n × κ) (Qubits n × κ) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (U ^ bitsToNat p.1) p.2 q.2 else 0

/-- de Wolf p.46 (§4.6, steps 1–4): the state of phase estimation before the final measurement:
from `|0ⁿ⟩|ψ⟩`, apply `F_{2ⁿ}` to the first register, the controlled powers `|j⟩|ψ⟩ ↦ |j⟩U^j|ψ⟩`,
and `F_{2ⁿ}^{−1}` to the first register. The law of the measured estimate is `marginalFst`. -/
noncomputable def phaseEstimationState {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (U : Matrix κ κ ℂ) (ψ : EuclideanSpace ℂ κ) : EuclideanSpace ℂ (Qubits n × κ) :=
  act (Matrix.kronecker (star (qftQubits n)) (1 : Matrix κ κ ℂ) * controlledPower n U *
    Matrix.kronecker (qftQubits n) (1 : Matrix κ κ ℂ)) (tensorVec (zeroKet n) ψ)

/-- de Wolf p.50 (§5.2, the period-finding problem): `f` has period `r`: `f(a) = f(b)` iff
`a = b mod r`. (The problem adds `r ∈ {1, …, N}` and `f : ℕ → {0, …, N − 1}`.) -/
def HasPeriod (f : ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ a b, f a = f b ↔ a ≡ b [MOD r]

/-- de Wolf p.51 (§5.3: "pick some `q = 2^ℓ` such that `N² < q ≤ 2N²`"): `ℓ`, the least natural
number with `2^ℓ > N²` (`Nat.clog 2 (N² + 1)`); for `N ≥ 1`, `q = 2^ℓ` satisfies
`N² < q ≤ 2N²`. -/
def shorEll (N : ℕ) : ℕ :=
  Nat.clog 2 (N ^ 2 + 1)

/-- de Wolf p.51 (§5.3): one run of Shor's period-finding circuit before the measurements: from
`|0^ℓ⟩|0ⁿ⟩` (`ℓ = shorEll N`, `n = ⌈log N⌉ = Nat.clog 2 N`), apply `F_q` to the first register,
`O_f : |a⟩|y⟩ ↦ |a⟩|y ⊕ f(a)⟩` (`a` read as an integer, `f(a)` written in `n` bits), and `F_q` to
the first register. The law of the measured `b` is `marginalFst`, `b` read as `bitsToNat b`. -/
noncomputable def shorRunState (N : ℕ) (f : ℕ → ℕ) :
    EuclideanSpace ℂ (Qubits (shorEll N) × Qubits (Nat.clog 2 N)) :=
  act (Matrix.kronecker (qftQubits (shorEll N)) (1 : Matrix (Qubits (Nat.clog 2 N))
      (Qubits (Nat.clog 2 N)) ℂ) *
    xorOracle (fun a : Qubits (shorEll N) => natToBits (Nat.clog 2 N) (f (bitsToNat a))) *
    Matrix.kronecker (qftQubits (shorEll N)) (1 : Matrix (Qubits (Nat.clog 2 N))
      (Qubits (Nat.clog 2 N)) ℂ)) (ket (0, 0))

/-- de Wolf p.59 (§6.2.1): for `G = Z_{N_1} × ⋯ × Z_{N_l}`, the character
`χ_g(h) = Π_i ω_{N_i}^{g_i h_i} = Π_i e^{2πi g_i h_i / N_i}` (`g_i, h_i` read in `{0, …, N_i − 1}`). -/
noncomputable def abelianChar {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (g h : (i : Fin l) → ZMod (N i)) : ℂ :=
  ∏ i : Fin l, Complex.exp (2 * Real.pi * Complex.I * (((g i).val * (h i).val : ℕ) : ℂ) / (N i : ℂ))

/-- de Wolf p.59 (§6.2.1): the labels of `H^⊥ = {χ_g : χ_g(h) = 1 for all h ∈ H}`. -/
def annihilator {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (H : AddSubgroup ((i : Fin l) → ZMod (N i))) : Set ((i : Fin l) → ZMod (N i)) :=
  {g | ∀ h ∈ H, abelianChar g h = 1}

/-- de Wolf p.60 (§6.2.2): the QFT over `G = Z_{N_1} × ⋯ × Z_{N_l}`, `|k⟩ ↦ |χ_k⟩ =
|G|^{−1/2} Σ_g χ_k(g) |g⟩` (the tensor product `F_{N_1} ⊗ ⋯ ⊗ F_{N_l}`). -/
noncomputable def qftAbelian {l : ℕ} (N : Fin l → ℕ) [∀ i, NeZero (N i)] :
    Matrix ((i : Fin l) → ZMod (N i)) ((i : Fin l) → ZMod (N i)) ℂ :=
  Matrix.of fun g k =>
    ((Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i))))⁻¹ : ℂ) * abelianChar k g

/-- de Wolf p.58 (§6.1.2: "`f` is constant within each coset, and distinct on different cosets:
`f(g) = f(g')` iff `gH = g'H`"), Childs p.30 (§5.3): `f` hides the subgroup `H`:
`f x = f y ↔ x⁻¹ y ∈ H`. Both directions are required (trap Q17). The additive version
`AddHides` (`f x = f y ↔ −x + y ∈ H`) is de Wolf's `f(g) = f(g')` iff `g − g' ∈ H` for an
Abelian group. -/
@[to_additive AddHides]
def Hides {G S : Type*} [Group G] (f : G → S) (H : Subgroup G) : Prop :=
  ∀ x y, f x = f y ↔ x⁻¹ * y ∈ H

/-- de Wolf p.60 (§6.2.2, step 2), p.65 (§7.2): the uniform superposition
`|ι|^{−1/2} Σ_i |i⟩` over a finite index set. (For `n` qubits it is `H^{⊗n}|0ⁿ⟩`.) -/
noncomputable def uniformState (ι : Type*) [Fintype ι] : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun _ => ((Real.sqrt (Fintype.card ι))⁻¹ : ℂ)

/-- de Wolf p.60 (§6.2.2, steps 1–5): the state of the standard Abelian HSP algorithm before the
final measurement: the uniform superposition over `G` with `|0⟩` in the second register, one query
`|g, y⟩ ↦ |g, y + f(g)⟩`, then the QFT over `G` on the first register. (The step-4 measurement of
the second register does not change the law `marginalFst` of the first register; the answer set
`S` carries an Abelian group structure only to define the unitary query.) -/
noncomputable def hspStandardState {l : ℕ} (N : Fin l → ℕ) [∀ i, NeZero (N i)] {S : Type*}
    [AddCommGroup S] [Fintype S] [DecidableEq S] (f : ((i : Fin l) → ZMod (N i)) → S) :
    EuclideanSpace ℂ (((i : Fin l) → ZMod (N i)) × S) :=
  act (Matrix.kronecker (qftAbelian N) (1 : Matrix S S ℂ) * xorOracle f)
    (tensorVec (uniformState ((i : Fin l) → ZMod (N i))) (ket 0))

/-! ### Sanity tests -/

theorem qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) * (k : ℕ) : ℕ) : ℂ) /
      (N : ℂ)) / (Real.sqrt N : ℂ) := rfl

example : qftMatrix 1 = 1 := by
  ext j k
  fin_cases j; fin_cases k
  simp [qftMatrix]

/-- `F_2` is the Hadamard gate (de Wolf p.41), under `Fin 2 ≃ Bool`. -/
theorem qftMatrix_two (j k : Fin 2) : qftMatrix 2 j k = hadamard (finTwoEquiv j) (finTwoEquiv k) := by
  have hpi : Complex.exp (2 * Real.pi * Complex.I * 2⁻¹) = -1 := by
    rw [show (2 * Real.pi * Complex.I * 2⁻¹ : ℂ) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  fin_cases j <;> fin_cases k <;> simp [qftMatrix, hadamard, finTwoEquiv, div_eq_mul_inv, hpi]

/-- The one-qubit QFT is the Hadamard gate (de Wolf p.41: `F_2 = H`). -/
example (y z : Qubits 1) : qftQubits 1 y z = hadamard (y 0) (z 0) := by
  have hb : ∀ b : Qubits 1, (bitsEquivFin 1 b : Fin 2) = finTwoEquiv.symm (b 0) := by
    intro b
    apply Fin.ext
    rw [bitsEquivFin_apply]
    cases h : b 0 <;> simp only [bitsToNat, Fin.sum_univ_one, h] <;> rfl
  simp only [qftQubits, Matrix.submatrix_apply]
  rw [hb y, hb z]
  exact (qftMatrix_two (finTwoEquiv.symm (y 0)) (finTwoEquiv.symm (z 0))).trans (by simp)

/-- `shorEll` pins `q = 2^ℓ` with `N² < q ≤ 2N²`: at `N = 3`, `q = 16`. -/
example : shorEll 3 = 4 := by decide

example : shorEll 1 = 1 := by decide

example : HasPeriod (fun a => a % 3) 3 := fun _ _ => Iff.rfl

end QAlgorithms
