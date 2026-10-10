import QAlgorithms.Defs.PhaseOracles

/-!
# Gilyén, Arunachalam, Wiebe: Optimizing quantum optimization algorithms via faster quantum
gradient computation

A. Gilyén, S. Arunachalam, N. Wiebe, *Optimizing quantum optimization algorithms via faster
quantum gradient computation* (arXiv:1711.00465v3), cited "GAW p.N" (PDF pages).

Oracles are the frozen GAW objects: `IsGAWProbabilityOracle` (Definition 8, flag = last auxiliary
qubit), `IsGAWPhaseOracle` (Definition 10), `IsGAWFractionalOracle` (Definition 11). An algorithm
is a frozen `PhaseQueryCircuit`: oracle-independent unitaries interleaved with oracle
applications, fixed before the oracle (trap Q2); its query count `queryCount` counts every
application of the oracle (or its adjoint, controlled or not). Big-O bounds are unfolded as
`∃ C > 0` quantified before every parameter.
-/

namespace QAlgorithms.Papers.GAW19

universe u

/-- GAW p.18, Theorem 14 (probability oracle to approximate phase oracle). Let `p : X → [0, 1]` and
let `U_p` be a probability oracle for `p` with an `n`-qubit auxiliary space (`n = m + 1`, the flag
being the last qubit). For `ε ∈ (0, 1/3)` there is a circuit `O` with `a = O(log log(1/ε))` extra
qubits and `O(log(1/ε))` applications of `U_p` and `U_p†` such that for every phase oracle `O_p`
for `p` and every unit `ψ ∈ H`,
`‖O |ψ⟩|0⟩^{⊗(n+a)} − O_p |ψ⟩|0⟩^{⊗(n+a)}‖ ≤ ε`.

The circuit depends only on `ε`, `X` and `n`, never on `p` or `U_p`; its oracle applications are
uncontrolled (footnote 13: controlled `G_U` only controls the reflections). "For all `|ψ⟩ ∈ H`" is
read as unit `ψ` (the proof, eqs. (18)–(19), bounds the error for normalized `ψ`). -/
theorem probOracle_to_phaseOracle :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
      ∀ (X : Type u) [Fintype X] [DecidableEq X] (m : ℕ),
        ∃ a : ℕ, (a : ℝ) ≤ C * Real.log (Real.log (1 / ε)) ∧
          ∃ c : PhaseQueryCircuit X Unit (m + 1) a,
            (∀ s ∈ c, ∀ (r : Unit) (adj : Bool) (b : Fin a), s ≠ .query r adj (some b)) ∧
            (c.queryCount : ℝ) ≤ C * Real.log (1 / ε) ∧
            ∀ (p : X → ℝ) (Up : Matrix (X × Qubits (m + 1)) (X × Qubits (m + 1)) ℂ),
              IsGAWProbabilityOracle Up p →
              ∀ Op : Matrix (X × Qubits (m + 1 + a)) (X × Qubits (m + 1 + a)) ℂ,
                IsGAWPhaseOracle (fun _ => false) Op p →
                ∀ ψ : EuclideanSpace ℂ X, ‖ψ‖ = 1 →
                  ‖act (c.unitary fun _ => Up) (tensorVec ψ (ket fun _ => false)) -
                    act Op (tensorVec ψ (ket fun _ => false))‖ ≤ ε := by
  sorry

/-- GAW p.21, Lemma 16 (phase oracle to probability oracle; proof in Appendix B, pp.55–57). Let
`ε, δ ∈ (0, 1/2)` and `p : X → [δ, 1 − δ]`. Given a phase oracle `O_p` (with any `w`-qubit
auxiliary register), `O(log(1/ε)/δ)` invocations of the (controlled) `O_p` and `O_p†` implement
`U_p : |x⟩|0⟩^{⊗k}|0⟩ ↦ |x⟩ ⊗ (√p′(x) |0⟩^{⊗k}|0⟩ + √(1 − p′(x)) |Φ^⊥⟩|1⟩)` with
`|√p′(x) − √p(x)| ≤ ε` for every `x ∈ X`.

Here `k = w + a`: the register `|0⟩^{⊗k}` holds the oracle's `w` auxiliary qubits and `a` extra
ones, and the last qubit is the flag. The source's "for every `x ∈ ℝⁿ`" is a typo for `x ∈ X` (the
lemma's domain). The displayed map (good amplitude on `|0^k⟩` with flag `0`) is stated literally;
`|Φ^⊥⟩` is a unit vector. The circuit is fixed before `p` and `O_p` (trap Q2). -/
theorem phaseOracle_to_probOracle :
    ∃ C : ℝ, 0 < C ∧ ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
      ∀ (X : Type u) [Fintype X] [DecidableEq X] (w : ℕ),
        ∃ (a : ℕ) (c : PhaseQueryCircuit X Unit w (a + 1)),
          (c.queryCount : ℝ) ≤ C * Real.log (1 / ε) / δ ∧
          ∀ p : X → ℝ, (∀ x, δ ≤ p x ∧ p x ≤ 1 - δ) →
            ∀ Op : Matrix (X × Qubits w) (X × Qubits w) ℂ,
              IsGAWPhaseOracle (fun _ => false) Op p →
              ∀ x : X, ∃ p' : ℝ, 0 ≤ p' ∧ p' ≤ 1 ∧ |Real.sqrt p' - Real.sqrt (p x)| ≤ ε ∧
                ∃ Φ : EuclideanSpace ℂ (Qubits (w + a)), ‖Φ‖ = 1 ∧
                  act (c.unitary fun _ => Op) (ket (x, fun _ => false)) =
                    (tensorVec (ket x)
                      ((Real.sqrt p' : ℂ) • snocQubit (zeroKet (w + a)) false +
                        (Real.sqrt (1 - p') : ℂ) • snocQubit Φ true) :
                      EuclideanSpace ℂ (X × Qubits (w + (a + 1)))) := by
  sorry

/-- GAW p.28, Theorem 23 (gradient estimation with phase queries). Let `m ∈ ℤ₊`, `R > 0`,
`B ≥ 0`, and let `f : [−R, R]^d → ℝ` be given with (fractional) phase oracle access. If `f` is
`(2m + 1)`-times differentiable and `|∂_r^{2m+1} f(x)| ≤ B` for all `x ∈ [−R, R]^d`, `r = x/‖x‖`,
then an approximate gradient `g` with `‖g − ∇f(0)‖_∞ ≤ ε` is computed with probability at least
`1 − ρ` using
`O((max(√d/ε · (B√d/ε)^{1/(2m)}, m/(εR)) log(2m) + m) log(d/ρ))` phase queries.

Model: the algorithm chooses finitely many distinct query points `pt j ∈ [−R, R]^d`, a start
state, a circuit of uncontrolled, non-adjoint fractional queries `O^r_f`, `r ∈ [−1, 1]` (each one
query, eq. (25) p.30), and a classical post-processing `out` of the final computational-basis
measurement; all of this before `f` and the oracle. Pinned readings (recorded in STATUS.md):
the algorithm is built for a known bound `‖∇f(0)‖_∞ ≤ M` (Theorem 21, p.26, which the proof
uses; the query count is `M`-independent), and the factor `log(d/ρ)` is read as
`1 + log(d/ρ)` (the proof repeats `⌈C log(d/ρ)⌉ ≥ 1` times). "(2m + 1)-times differentiable" is
differentiability within the cube of the derivatives of order `≤ 2m`; the directional
derivative is taken within the cube along the ray (Definition 6, p.12), for `x ≠ 0`. -/
theorem gradient_phaseQueries :
    ∃ C : ℝ, 0 < C ∧ ∀ (d m : ℕ), 1 ≤ m → ∀ R B ε ρ M : ℝ, 0 < R → 0 ≤ B → 0 < ε →
      0 < ρ → ρ < 1 → 0 < M → ∀ w : ℕ,
        ∃ (N : ℕ) (pt : Fin N → Fin d → ℝ), Function.Injective pt ∧
          (∀ j, pt j ∈ Set.univ.pi fun _ : Fin d => Set.Icc (-R) R) ∧
          ∃ (a : ℕ) (c : PhaseQueryCircuit (Fin N) (Set.Icc (-1 : ℝ) 1) w a)
            (ψ0 : EuclideanSpace ℂ (Fin N × Qubits (w + a)))
            (out : Fin N × Qubits (w + a) → Fin d → ℝ),
            ‖ψ0‖ = 1 ∧
            (∀ s ∈ c, ∀ (r : Set.Icc (-1 : ℝ) 1) (adj : Bool) (b : Option (Fin a)),
              s = .query r adj b → adj = false ∧ b = none) ∧
            (c.queryCount : ℝ) ≤ C * ((max (Real.sqrt d / ε * (B * Real.sqrt d / ε) ^ (1 / (2 * (m : ℝ))))
                (m / (ε * R)) * Real.log (2 * m) + m) * (1 + Real.log (d / ρ))) ∧
            ∀ f : (Fin d → ℝ) → ℝ,
              (∀ j < 2 * m + 1, DifferentiableOn ℝ
                (iteratedFDerivWithin ℝ j f (Set.univ.pi fun _ : Fin d => Set.Icc (-R) R))
                (Set.univ.pi fun _ : Fin d => Set.Icc (-R) R)) →
              (∀ x ∈ Set.univ.pi (fun _ : Fin d => Set.Icc (-R) R), x ≠ 0 →
                |rayDeriv (2 * m + 1) f (Set.univ.pi fun _ : Fin d => Set.Icc (-R) R) x
                  ((euclidNorm x)⁻¹ • x)| ≤ B) →
              ‖(fun i => fderiv ℝ f 0 (Pi.single i 1) : Fin d → ℝ)‖ ≤ M →
              ∀ O : Set.Icc (-1 : ℝ) 1 → Matrix (Fin N × Qubits w) (Fin N × Qubits w) ℂ,
                IsGAWFractionalOracle (fun _ => false) O (fun j => f (pt j)) →
                probEvent (act (c.unitary O) ψ0)
                  (fun z => ‖out z - fun i => fderiv ℝ f 0 (Pi.single i 1)‖ ≤ ε) ≥ 1 - ρ := by
  sorry

/-- GAW p.28, the paragraph after Theorem 23 (polynomial case). Suppose `R = Θ(1)` and `f` is a
multivariate polynomial of degree `k`; then `m = ⌈k/2⌉` gives `B = 0` and the algorithm of
Theorem 23 uses `Õ((k/ε) log(d/ρ))` phase queries.

The constant `C` may depend on the fixed `R`; the hidden polylogarithmic factor is the `log(2k)`
that Theorem 23 gives with `m = ⌈k/2⌉`, `B = 0`, and `log(d/ρ)` is read as `1 + log(d/ρ)` as in
Theorem 23. "Degree `k`" is total degree at most `k`, `k ≥ 1` (so that `m ∈ ℤ₊`), and `ε ≤ 1`.
The algorithm model is that of Theorem 23, with the gradient bound `M` known in advance. -/
theorem gradient_phaseQueries_polynomial :
    ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧ ∀ (d k : ℕ), 1 ≤ k → ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 →
      0 < ρ → ρ < 1 → 0 < M → ∀ w : ℕ,
        ∃ (N : ℕ) (pt : Fin N → Fin d → ℝ), Function.Injective pt ∧
          (∀ j, pt j ∈ Set.univ.pi fun _ : Fin d => Set.Icc (-R) R) ∧
          ∃ (a : ℕ) (c : PhaseQueryCircuit (Fin N) (Set.Icc (-1 : ℝ) 1) w a)
            (ψ0 : EuclideanSpace ℂ (Fin N × Qubits (w + a)))
            (out : Fin N × Qubits (w + a) → Fin d → ℝ),
            ‖ψ0‖ = 1 ∧
            (∀ s ∈ c, ∀ (r : Set.Icc (-1 : ℝ) 1) (adj : Bool) (b : Option (Fin a)),
              s = .query r adj b → adj = false ∧ b = none) ∧
            (c.queryCount : ℝ) ≤ C * ((k : ℝ) / ε * Real.log (2 * k) * (1 + Real.log (d / ρ))) ∧
            ∀ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ k →
              ‖(fun i => fderiv ℝ (fun x => MvPolynomial.eval x P) 0 (Pi.single i 1) :
                Fin d → ℝ)‖ ≤ M →
              ∀ O : Set.Icc (-1 : ℝ) 1 → Matrix (Fin N × Qubits w) (Fin N × Qubits w) ℂ,
                IsGAWFractionalOracle (fun _ => false) O (fun j => MvPolynomial.eval (pt j) P) →
                probEvent (act (c.unitary O) ψ0)
                  (fun z => ‖out z - fun i => fderiv ℝ (fun x => MvPolynomial.eval x P) 0
                    (Pi.single i 1)‖ ≤ ε) ≥ 1 - ρ := by
  sorry

end QAlgorithms.Papers.GAW19
