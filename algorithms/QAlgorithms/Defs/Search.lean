import QAlgorithms.Defs.Fourier

/-!
# Grover search and amplitude amplification (shared definition layer)

The uniform superposition `uniformState` used here is defined in `QAlgorithms.Defs.Fourier`
(it is first needed by the Abelian HSP algorithm).
-/

namespace QAlgorithms

/-- de Wolf p.65 (§7.2, (7.1)): the Grover iterate `G = H^{⊗n} R_0 H^{⊗n} O_{x,±}` (one phase
query per iterate), with `R_0 = reflAt 0` leaving `|0ⁿ⟩` fixed and negating every other basis
state. -/
noncomputable def groverIterate {n : ℕ} (x : Qubits n → Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  hadamardN n * reflAt (0 : Qubits n) * hadamardN n * phaseOracle x

/-- de Wolf p.65–66 (§7.2): `P_k`, the probability that measuring `G^k H^{⊗n} |0ⁿ⟩` gives a
solution (an `i` with `x_i = 1`). -/
noncomputable def groverSuccessProb {n : ℕ} (x : Qubits n → Bool) (k : ℕ) : ℝ :=
  probEvent (act (groverIterate x ^ k) (act (hadamardN n) (zeroKet n))) fun i => x i = true

/-- de Wolf p.66 (§7.2: "`θ = arcsin √(t/N)`"), p.69 (§7.3, with `p` in place of `t/N`): Grover's
angle. The quotient is real division; statements take `N ≥ 1` (here `N = 2ⁿ`) and require
`1 ≤ t` before dividing by `θ`. -/
noncomputable def groverAngle (t N : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt ((t : ℝ) / (N : ℝ)))

/-- de Wolf p.69 (§7.3): the amplitude-amplification iterate `A R_0 A^{−1} R_G` (first the
reflection `R_G` through the bad state, then the reflection `A R_0 A^{−1}` through `A|0^m⟩`),
with `A` unitary so that `A^{−1} = A†`, and `R_0 = reflAt z` for `z = 0^m`. -/
def ampAmpIterate {ι : Type*} [Fintype ι] [DecidableEq ι] (A RG : Matrix ι ι ℂ) (z : ι) :
    Matrix ι ι ℂ :=
  A * reflAt z * star A * RG

/-! ### Sanity tests -/

/-- With no iterates, `P_0` is the probability of a solution in the uniform superposition. -/
example {n : ℕ} (x : Qubits n → Bool) :
    groverSuccessProb x 0 = probEvent (act (hadamardN n) (zeroKet n)) fun i => x i = true := by
  simp [groverSuccessProb, act]

/-- de Wolf p.67: for `t = N/4`, `θ = π/6`. -/
example : groverAngle 1 4 = Real.pi / 6 := by
  rw [groverAngle, show ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num), show (1 / 2 : ℝ) = Real.sin (Real.pi / 6) by
      rw [Real.sin_pi_div_six]]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Grover is amplitude amplification with `A = H^{⊗n}` and `R_G = O_{x,±}` (de Wolf p.69), as
`H^{⊗n}` is self-adjoint. -/
example {n : ℕ} (x : Qubits n → Bool) :
    ampAmpIterate (hadamardN n) (phaseOracle x) 0 = groverIterate x := by
  simp [ampAmpIterate, groverIterate, hadamardN_star]

end QAlgorithms
