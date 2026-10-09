import QAlgorithms.Defs.GradientMethods

/-!
# Nannicini, Chapter 5 (part a): the quantum gradient algorithm and state tomography

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Proposition 5.3 (p.106–108), Proposition 5.6 (p.109–111), Proposition 5.16
(p.115), Corollary 5.18 (p.116–117). Proposition 5.25 (p.120–121) is not stated (see `HARD.md`).

Conventions. A collection of `d` registers of `q` qubits each is indexed by `Fin d → Qubits q`
(register `i` is the source's register `i + 1`); a `q`-bit string is read as an integer most
significant bit first (`bitsToNat`). The binary oracle of Def. 5.1 is the frozen `modAddOracle`,
Jordan's circuit (Fig. 5.1) is the frozen `jordanGradientState`, Alg. 3 is the frozen
`gradientAlgState`, the grid `G_q` is `gridPoint`, Fig. 5.3 is the frozen `hadamardTestCircuit`,
and Def. 5.9 is the frozen `IsProbabilityOracle`.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.108, Proposition 5.3 (Jordan's gradient algorithm, exactly linear case). Let
`U_f |x_1⟩⋯|x_d⟩|y⟩ = |x_1⟩⋯|x_d⟩|y ⊞ f(x_1, …, x_d)⟩` be the binary oracle of Def. 5.1 (p.106),
every register on `q` qubits, `⊞` addition modulo `2^q`. Assume `f` is linear,
`f(x) = ⟨g, x⟩ + b`, where `x = (x_1, …, x_d)` are the integers written in the `d` input
registers (Eq. (5.1)), and that every component `g_i` of the gradient is exactly representable on
`q` bits (`g_i` is the integer of a `q`-bit string) and `b` is a nonnegative integer (so that
`f(x)` is an integer; it enters the register modulo `2^q`). Then the circuit of Fig. 5.1 (start
in `|0⟩^{⊗d} ⊗ |1⃗⟩`, apply `H^{⊗q}` to the first `d` registers and `Q_q` to the last, one
application of `U_f`, then `Q_q†` on each of the first `d` registers) yields the gradient: the
measurement of the first `d` registers returns `(g_1, …, g_d)` with probability `1`. The single
application of `U_f` is structural in `jordanGradientState`. -/
theorem jordanGradient_exact (d q : ℕ) (g : Fin d → Qubits q) (b : ℕ) :
    let F : (Fin d → Qubits q) → ℕ := fun x => ∑ i, bitsToNat (g i) * bitsToNat (x i) + b
    marginalFst (jordanGradientState d q F) g = 1 := by
  sorry

/-- Nannicini p.110, Proposition 5.6 (based on Lem. 5.1 of Gilyén et al. 2019). Let `q > 0`,
`b ∈ ℝ`, `g ∈ ℝ^d` with `‖g‖_∞ ≤ 1/3`, and `f : [−1/2, 1/2]^d → ℝ` (taken on `ℝ^d`; only its
values on the grid are used). Let `G_q = {j/2^q − 1/2 + 1/2^{q+1} : j = 0, …, 2^q − 1}` (p.109)
and `x̂` the grid point of the register contents `x`. If `|f(x̂) − ⟨g, x̂⟩ − b| ≤ 1/(20π2^q)` for at
least `99.9%` of the `2^{dq}` points `x̂ ∈ G_q^d`, then the output `g̃ = (k̂_1, …, k̂_d)` of the
gradient algorithm (Alg. 3, p.110: `H^{⊗q}` on each of `d` registers in `|0⟩`, the phase oracle
`|x⟩ ↦ e^{2πi 2^q f(x̂)}|x⟩`, `Q_{G_q}†` on each register, measure) satisfies
`Pr(|g̃_j − g_j| ≤ 1/2^q) > 3/5` for every `j = 1, …, d`. -/
theorem gradientAlg_approxLinear (d q : ℕ) (hq : 0 < q) (b : ℝ) (g : Fin d → ℝ)
    (hg : ∀ i, |g i| ≤ 1 / 3) (f : (Fin d → ℝ) → ℝ)
    (hf : (999 / 1000 : ℝ) * (2 : ℝ) ^ (d * q) ≤
      ((Finset.univ.filter fun x : Fin d → Qubits q =>
          |f (fun i => gridPoint q (x i)) - ∑ i, g i * gridPoint q (x i) - b| ≤
            1 / (20 * Real.pi * (2 : ℝ) ^ q)).card : ℝ)) :
    ∀ j : Fin d, 3 / 5 < probEvent (gradientAlgState d q f)
      fun k => |gridPoint q (k j) - g j| ≤ 1 / (2 : ℝ) ^ q := by
  sorry

/-- Nannicini p.115, Proposition 5.16 (Hadamard-test probability oracle). Let `U` be a unitary on
`n` qubits with `U|0⟩ = |ψ⟩`, and `V` a unitary on the `n`-qubit register together with an input
register `|x⟩` (basis `X`) with `V|0⟩|x⟩ = |ϕ_x⟩|x⟩` for every `x`. Then the circuit of Fig. 5.3
(on the flag qubit: `H`, `X`, controlled-`U`, `X`, controlled-`V`, `H`, `X`) is a probability oracle
(Def. 5.9) for `f(x) = (1 + Re⟨ψ|ϕ_x⟩)/2`. Its single application of controlled-`U` and of
controlled-`V` and its five single-qubit gates are structural in `hadamardTestCircuit`. -/
theorem hadamardTest_probabilityOracle {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Qubits n) (Qubits n) ℂ) (V : Matrix (Qubits n × X) (Qubits n × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hV : V ∈ Matrix.unitaryGroup (Qubits n × X) ℂ)
    (ϕ : X → EuclideanSpace ℂ (Qubits n))
    (hϕ : ∀ x, act V (ket ((0 : Qubits n), x)) = tensorVec (ϕ x) (ket x)) :
    IsProbabilityOracle (0 : Qubits n) (hadamardTestCircuit U V)
      (fun x => (1 + (inner ℂ (act U (zeroKet n)) (ϕ x)).re) / 2) := by
  sorry

/-- Nannicini p.117, Corollary 5.18 (pure-state tomography with Euclidean error). Let
`U|0⟩ = |ψ⟩ = ∑_{j ∈ {0,1}^n} α_j |j⟩` and `d = 2^n`. With probability at least `1 − δ` one
outputs `α̃ ∈ ℝ^d` with `‖Re(α) − α̃‖ ≤ ϵ` using `Õ(d/ϵ)` applications of `U` and `U†` and
`Õ(d²/ϵ)` additional gates; a small modification outputs `α̃` with `‖Im(α) − α̃‖ ≤ ϵ` with the
same running time. Formally: there are constants `C > 0` and `c` such that for every `n`, every
`ϵ > 0` and every `δ ∈ (0, 1)` there is an oracle circuit over the gate set `{H, T, CX}` of
Thm. 1.43, on a workspace of `w` qubits started in `|0⟩`, with oracle calls to `U` (possibly
controlled, possibly adjoint), together with a classical read-out `out` of the measured
workspace, using at most `C (d/ϵ) L` oracle calls and `C (d²/ϵ) L` gates, where
`L = (log(2 + d/ϵ) + log(2 + 1/δ))^c` is the polylogarithmic factor of `Õ` (Def. 1.11), such that
for **every** unitary `U` on `n` qubits the Euclidean error `‖Re(α) − out(z)‖ ≤ ϵ` holds with
probability at least `1 − δ`; and a second such circuit for `Im(α)`. The circuit is chosen before
`U` and sees `U` only through its oracle calls (trap Q2). -/
theorem stateTomography_euclidean :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ → δ < 1 →
      (∃ (w : ℕ) (circ : OracleCircuit htcxGateSet (fun _ : Fin 1 => n) w)
          (out : Qubits w → Qubits n → ℝ),
        (circ.queryCount 0 : ℝ) ≤
            C * ((2 : ℝ) ^ n / ε) * (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          (circ.gateCount : ℝ) ≤
            C * (((2 : ℝ) ^ n) ^ 2 / ε) *
              (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          ∀ U ∈ Matrix.unitaryGroup (Qubits n) ℂ,
            1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
              fun z => Real.sqrt (∑ j, ((act U (zeroKet n) j).re - out z j) ^ 2) ≤ ε) ∧
      (∃ (w : ℕ) (circ : OracleCircuit htcxGateSet (fun _ : Fin 1 => n) w)
          (out : Qubits w → Qubits n → ℝ),
        (circ.queryCount 0 : ℝ) ≤
            C * ((2 : ℝ) ^ n / ε) * (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          (circ.gateCount : ℝ) ≤
            C * (((2 : ℝ) ^ n) ^ 2 / ε) *
              (Real.log (2 + (2 : ℝ) ^ n / ε) + Real.log (2 + 1 / δ)) ^ c ∧
          ∀ U ∈ Matrix.unitaryGroup (Qubits n) ℂ,
            1 - δ ≤ probEvent (act (circ.unitary fun _ => U) (zeroKet w))
              fun z => Real.sqrt (∑ j, ((act U (zeroKet n) j).im - out z j) ^ 2) ≤ ε) := by
  sorry

end QAlgorithms.Nannicini
