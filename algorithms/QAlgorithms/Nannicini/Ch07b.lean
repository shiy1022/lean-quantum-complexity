import QAlgorithms.Defs.Adiabatic

/-!
# Nannicini, Chapter 7 (second part): block-encodings, Gibbs states, trace estimation

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §7.2.4. Block-encodings are the frozen `IsBlockEncoding` (Def. 7.11, auxiliary
register first). A register of `m + k` qubits is split into its first `m` and last `k` qubits by
`qubitsAppendEquiv m k`. `Õ(g)` (Def. 1.11, p.11) is unfolded as `C · g · polylog`, with the
constants `C, c` quantified before every parameter.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.171, Lemma 7.37 (Lem. 4.14 in [van Apeldoorn, 2020]). Let `ξ ∈ (0, 1/6]` and
`β ≥ 1`. There is a polynomial `P` with `|P(x) − exp(2βx)/4| ≤ ξ` for all `x ∈ [−1, 0]`,
`|P(x)| ≤ 1/2` for all `x ∈ [−1, 1]`, and `deg P = Õ(β)`. The `Õ(β)` is
`C β (log(2 + β) + log(2 + 1/ξ))^c` with absolute constants `C > 0`, `c`, chosen before `ξ`, `β`
(Def. 1.11: polylogarithmic dependence on the other parameter `1/ξ` is allowed). -/
theorem expPoly_approx :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ ξ β : ℝ, 0 < ξ → ξ ≤ 1 / 6 → 1 ≤ β →
      ∃ P : Polynomial ℝ,
        (∀ x ∈ Set.Icc (-1 : ℝ) 0, |P.eval x - Real.exp (2 * β * x) / 4| ≤ ξ) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 / 2) ∧
        (P.natDegree : ℝ) ≤ C * β * (Real.log (2 + β) + Real.log (2 + 1 / ξ)) ^ c := by
  sorry

/-- Nannicini p.172, Lemma 7.39 (Lem. 6.4.4 in [Gilyén, 2019]), stated for a normalized density
matrix. Let `U` be a `(q + a)`-qubit unitary such that `U|0⟩_q|0⟩_a = |ϱ⟩` is a purification of the
`q`-qubit density matrix `ρ` (Def. 1.69, p.40: tracing out the last `a` qubits of `|ϱ⟩⟨ϱ|` gives
`ρ`). Then there is a circuit, fixed before `U` and `ρ`, using `U` once, `U†` once (uncontrolled)
and at most `q + 1` two-qubit gates on `(q + a) + q` wires, whose unitary is a
`(1, q + a, 0)`-block-encoding of `ρ` (auxiliary register = the first `q + a` wires).

Discrepancy with the page (trap 30): the source allows a subnormalized `ρ` (Def. 7.35). In that
case the claim fails in the stated resources: with the auxiliary register of `q + a` qubits
starting and ending in `|0⟩`, the block entries of any such circuit are `⟨ϱ, x|S|ϱ, y⟩` for a
unitary `S`, and equating them with the `|0⟩_B`-block of the partial trace for every `U` forces
`S` to vanish on the `|1⟩_B` branch. The normalized case is the one the construction
`(U† ⊗ I)(SWAP ⊗ I)(U ⊗ I)` proves. -/
theorem densityMatrix_blockEncoding (q a : ℕ) :
    ∃ c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => q + a) ((q + a) + q),
      (c.countP fun s => match s with
        | OracleStep.query _ false _ _ _ => true
        | _ => false) ≤ 1 ∧
      (c.countP fun s => match s with
        | OracleStep.query _ true _ _ _ => true
        | _ => false) ≤ 1 ∧
      (∀ s ∈ c, match s with
        | OracleStep.query _ _ ctrl _ _ => ctrl = none
        | OracleStep.gate _ => True) ∧
      c.gateCount ≤ q + 1 ∧
      ∀ (U : Matrix (Qubits (q + a)) (Qubits (q + a)) ℂ) (ρ : Matrix (Qubits q) (Qubits q) ℂ),
        U ∈ Matrix.unitaryGroup (Qubits (q + a)) ℂ → IsDensityMatrix ρ →
        traceRight (pureDensity (WithLp.toLp 2 fun p : Qubits q × Qubits a =>
          act U (zeroKet (q + a)) ((qubitsAppendEquiv q a).symm p))) = ρ →
        IsBlockEncoding (0 : Qubits (q + a))
          ((c.unitary fun _ => U).submatrix (qubitsAppendEquiv (q + a) q).symm
            (qubitsAppendEquiv (q + a) q).symm) 1 0 ρ := by
  sorry

/-- Nannicini p.173, Proposition 7.41 (Cor. 6.4.5 in [Gilyén, 2019]). Let `ρ` be a `q`-qubit
density matrix and `U` an `(α, a, θ/2)`-block-encoding of a Hermitian matrix
`A ∈ ℝ^{2^q × 2^q}` with `‖A‖ ≤ 1`. A quantum circuit (fixed before `A`, `U`, `ρ`) acting on one
copy of `ρ` and `w` ancillas in `|0⟩`, followed by a measurement of all qubits and a classical
map `Y` of the outcome (Rem. 7.42), outputs a sample of a random variable `Y` with
`|E[Y] − Tr(Aρ)| ≤ θ/4` and `Var[Y] ≤ C` (`σ = O(1)`). It uses `Õ(α)` applications of `U`
and `U†` and `Õ(α)` two-qubit gates, with
`Õ(α) = C(α + 1)(log(2 + α) + log(2 + 1/θ) + log(2 + q) + log(2 + a))^c` (Def. 1.11, p.11: the
polylog factor may also depend on the other instance parameters `θ`, `q`, `a`).

Discrepancy with the page (trap 30): the gate count carries a factor `a + 1` (the number of
auxiliary qubits of `U`). Every block-encoding manipulation of the proof (amplification,
polynomial transformations) reflects about `|0⟩_a` once per use of `U`, which costs `Θ(a)`
two-qubit gates; the source's own Prop. 7.38 counts `Õ(√n β a)` gates, and the cited result
counts `O(a α log(1/θ))`. A bound `Õ(α)` polylogarithmic in `a` is not what the construction
gives. -/
theorem traceEstimator :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (q a : ℕ) (α θ : ℝ), 0 < α → 0 < θ →
      ∃ (w : ℕ) (V : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (q + w))
        (Y : Qubits (q + w) → ℝ),
        (V.queryCount 0 : ℝ) ≤ C * (α + 1) * (Real.log (2 + α) + Real.log (2 + 1 / θ) +
          Real.log (2 + (q : ℝ)) + Real.log (2 + (a : ℝ))) ^ c ∧
        (V.gateCount : ℝ) ≤
          C * (α + 1) * ((a : ℝ) + 1) * (Real.log (2 + α) + Real.log (2 + 1 / θ) +
            Real.log (2 + (q : ℝ)) + Real.log (2 + (a : ℝ))) ^ c ∧
        ∀ (A : Matrix (Qubits q) (Qubits q) ℂ) (U : Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
          (ρ : Matrix (Qubits q) (Qubits q) ℂ),
          A.IsHermitian → (∀ i j, (A i j).im = 0) → specNorm A ≤ 1 →
          IsBlockEncoding (0 : Qubits a)
            (U.submatrix (qubitsAppendEquiv a q).symm (qubitsAppendEquiv a q).symm) α (θ / 2) A →
          IsDensityMatrix ρ →
          |densityMean ((V.unitary fun _ => U) * withZeroAncillas ρ w *
              star (V.unitary fun _ => U)) Y - (A * ρ).trace.re| ≤ θ / 4 ∧
          densityVariance ((V.unitary fun _ => U) * withZeroAncillas ρ w *
              star (V.unitary fun _ => U)) Y ≤ C := by
  sorry

end QAlgorithms.Nannicini
