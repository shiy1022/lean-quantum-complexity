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

/-- Nannicini p.170, Definition 7.31 (trace norm): `‖A‖_Tr = Tr √(A†A)`, the sum of the singular
values of `A`, i.e. of the square roots of the eigenvalues of the Hermitian matrix `A†A`. -/
noncomputable def traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ∑ k, Real.sqrt (ascEigenvalues (A.conjTranspose * A) k)

/-- Corrected statement. Nannicini p.171, Proposition 7.38 (Lem. 4.15 in [van Apeldoorn, 2020]),
as printed: "Let `H ∈ ℝ^{n×n}` be a Hermitian matrix. Let `θ ∈ (0, 1/3]`, `β > 1`, and let `d`
be the degree of the polynomial from Lemma 7.37 when we let `ξ = θ/(128n)`. Let `U` be a
`(β, a, θ²β/(1024² d² n²))`-block-encoding of `H`. Then we can create a purification of a state
`ρ̃` such that `‖ρ̃ − exp(H)/Tr(exp(H))‖_Tr ≤ θ` using `Õ(√n β)` applications of `U` and
`Õ(√n β a)` elementary gates."

What was changed. (1) "The polynomial from Lemma 7.37" is a named parameter `P`: the statement
holds for every real polynomial with the three properties of Lemma 7.37 at `ξ = θ/(128n)`,
the degree bound `deg P ≤ C₀ β (log(2+β) + log(2+1/ξ))^{c₀}` (Lemma 7.37's `Õ(β)`) being stated
with constants `C₀, c₀` quantified universally before the theorem's own constants; `d` is
`deg P`, and the circuit may depend on `P` (it implements `P` by singular value transformation,
p.171–172). (2) `n = 2^q`, the case the source's own construction treats ("assume `n = 2^q` for
simplicity", p.171–172); a matrix of non-power-of-two size has no qubit block-encoding without a
padding convention the source does not give. (3) The gate bound carries `(a + 1)` instead of `a`,
so that it is not `0` at `a = 0`. (4) `Õ(·)` is `C · (·) · L^c` with
`L = log(2+n) + log(2+β) + log(2+1/θ) + log(2+a)` (Def. 1.11).

Why. Lemma 7.37 asserts only that some polynomial of degree `Õ(β)` exists, so "its degree `d`"
is not determined. The construction uses one such polynomial and needs the block-encoding
precision for the degree of the polynomial it uses; the universally quantified `P` is that
reading, made explicit.

Precision formulas checked against the rendered PDF page p.171 (2026-10-09): `ξ = θ/(128n)`,
block-encoding error `θ²β/(1024² d² n²)`, `θ ∈ (0, 1/3]` (closed at `1/3`, as in the rendered
page and the text layer). The first statement of this item had `θ²/(128n)` and
`θ²/(1024 d β² n²)`, read from a garbled text extraction.

Model. "Elementary gates" are two-qubit gates (`twoQubitGateSet`, as for Prop. 7.41). The circuit
acts on the `q` system qubits and `m` further qubits, all starting in `|0⟩`, and calls `U`
(acting on `a + q` qubits, auxiliary register first as in Def. 7.11) and `U†`. The created pure
state `V(U)|0⟩` is a purification (Def. 1.69) of `ρ̃`: `ρ̃` is its partial trace over the last
`m` qubits. `H` is real (`H ∈ ℝ^{n×n}`) and Hermitian. The Gibbs state is the frozen
`gibbsState` (Def. 7.34), the trace norm is `traceNorm` (Def. 7.31). -/
theorem gibbsState_preparation :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (q a : ℕ) (θ β : ℝ), 0 < θ → θ ≤ 1 / 3 →
      1 < β → ∀ P : Polynomial ℝ,
      (∀ x ∈ Set.Icc (-1 : ℝ) 0,
        |P.eval x - Real.exp (2 * β * x) / 4| ≤ θ / (128 * (2 : ℝ) ^ q)) →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 / 2) →
      (P.natDegree : ℝ) ≤
        C₀ * β * (Real.log (2 + β) + Real.log (2 + 1 / (θ / (128 * (2 : ℝ) ^ q)))) ^ c₀ →
      ∃ (m : ℕ) (V : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (q + m)),
        (V.queryCount 0 : ℝ) ≤ C * Real.sqrt ((2 : ℝ) ^ q) * β *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + β) + Real.log (2 + 1 / θ) +
            Real.log (2 + (a : ℝ))) ^ c ∧
        (V.gateCount : ℝ) ≤ C * Real.sqrt ((2 : ℝ) ^ q) * β * ((a : ℝ) + 1) *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + β) + Real.log (2 + 1 / θ) +
            Real.log (2 + (a : ℝ))) ^ c ∧
        ∀ (H : Matrix (Qubits q) (Qubits q) ℂ) (U : Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ),
          H.IsHermitian → (∀ i j, (H i j).im = 0) →
          IsBlockEncoding (0 : Qubits a)
            (U.submatrix (qubitsAppendEquiv a q).symm (qubitsAppendEquiv a q).symm) β
            (θ ^ 2 * β / (1024 ^ 2 * (P.natDegree : ℝ) ^ 2 * ((2 : ℝ) ^ q) ^ 2)) H →
          traceNorm (traceRight (pureDensity (WithLp.toLp 2 fun z : Qubits q × Qubits m =>
              act (V.unitary fun _ => U) (zeroKet (q + m)) ((qubitsAppendEquiv q m).symm z))) -
            gibbsState H) ≤ θ := by
  sorry

/-- Nannicini p.128, Definition 5.39 (QRAM), for the statement of Prop. 7.29 (chunk-local copy of
the object of the Cor. 5.45 chunk, which a chunk may not import): for stored words
`M_j ∈ {0,1}^r`, `U_QRAM |j⟩|y⟩ = |j⟩|y ⊕ M_j⟩` for all addresses `j ∈ {0,1}^b`,
`y ∈ {0,1}^r`. Address register first. Its size in the sense of Def. 5.39 is `2^b · r`. -/
noncomputable def qramOp (b r : ℕ) (M : Qubits b → Qubits r) :
    Matrix (Qubits (b + r)) (Qubits (b + r)) ℂ :=
  Matrix.reindex (qubitsAppendEquiv b r).symm (qubitsAppendEquiv b r).symm (xorOracle M)

/-- One classical arithmetic operation: the cost model for "`Õ(d²)` classical arithmetic
operations to initialize the QRAM data structures" of Nannicini p.168, Prop. 7.29, which the
source does not define (chunk-local copy of the model of the Cor. 5.45 chunk). A program is a
straight-line program over the reals: each instruction reads earlier values by index and appends
one new value; each counts as one operation. The operations are those of the preprocessing of
Cor. 5.45 (p.124, p.129–130), run for the `d` columns and the vector of column norms (p.168–169):
`+, −, ×, ÷, √, arccos`, the argument of a complex number, and rational constants. -/
inductive ArithOp where
  | const (c : ℚ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | div (i j : ℕ)
  | sqrt (i : ℕ)
  | arccos (i : ℕ)
  | arg (i j : ℕ)

/-- The value an instruction appends, given the values computed so far (an out-of-range index
reads `0`; `t / 0 = 0` as in Lean). `arg i j` is the argument of `vals[i] + i·vals[j]`. -/
noncomputable def ArithOp.value (vals : List ℝ) : ArithOp → ℝ
  | .const c => (c : ℝ)
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .sub i j => vals.getD i 0 - vals.getD j 0
  | .mul i j => vals.getD i 0 * vals.getD j 0
  | .div i j => vals.getD i 0 / vals.getD j 0
  | .sqrt i => Real.sqrt (vals.getD i 0)
  | .arccos i => Real.arccos (vals.getD i 0)
  | .arg i j => Complex.arg ⟨vals.getD i 0, vals.getD j 0⟩

/-- All values of a straight-line program run on an input list (inputs first, then one value per
instruction). The cost of the program is its length. -/
noncomputable def arithExec (Prog : List ArithOp) (input : List ℝ) : List ℝ :=
  Prog.foldl (fun vals g => vals ++ [g.value vals]) input

/-- The classical description of `A ∈ ℂ^{d×d}` given to the preprocessing: row by row, the list
`Re a_00, Im a_00, Re a_01, Im a_01, …`. -/
noncomputable def matrixInput {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : List ℝ :=
  (List.ofFn fun i => (List.ofFn fun j => [(A i j).re, (A i j).im]).flatten).flatten

/-- The QRAM contents written by the classical preprocessing (Rem. 5.40: classical write): word
`j` is the `r`-bit binary expansion (most significant bit first) of the integer part of the
program value with index `addr j`. Storing a value is not an arithmetic operation. -/
noncomputable def qramMatrixWords (b r : ℕ) (Prog : List ArithOp) (addr : Qubits b → ℕ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : Qubits b → Qubits r :=
  fun j => natToBits r ⌊(arithExec Prog (matrixInput A)).getD (addr j) 0⌋₊

/-- Corrected statement. Nannicini p.168, Proposition 7.29 (adapted from [Chakraborty et al.,
2019, Kerenidis and Prakash, 2017]), as printed: "Let `d = 2^q` and `A ∈ ℂ^{d×d}`. Suppose we
have a classical finite-precision description of the entries of `A` with `p` bits each, and
assume `p = Õ(1)`. Then, given a QRAM of size `O(d²p)`, we can implement a
`(‖A‖_F, Õ(q), ξ)`-block-encoding of `A` using `Õ(1)` accesses to the QRAM and additional gates,
and `Õ(d²)` classical arithmetic operations to initialize the QRAM data structures."

What was changed. (1) Cost model: "classical arithmetic operations" are counted in the
straight-line real-arithmetic model `ArithOp` (one operation per `+, −, ×, ÷, √, arccos, arg`
or constant); the QRAM of Def. 5.39 (`qramOp`) is written classically from the program's values
(`qramMatrixWords`); the circuit, the program and the addressing are fixed before `A`, which
enters only through the QRAM contents. (2) "`p = Õ(1)`" is the hypothesis
`p ≤ C₀ (log(2+d) + log(2+1/ξ))^{c₀}`, with `C₀, c₀` quantified universally before the theorem's
constants: polylogarithmic in `d` and `1/ξ`, the reading of p.168 ("the required precision is
only polylogarithmically large"). (3) "`p` bits each" is the magnitude bound
`|Re a_ij|, |Im a_ij| ≤ 2^p`, which every `p`-bit fixed-point description satisfies wherever its
binary point sits; the statement is for every such `A`. (4) The dependence on `ξ` is explicit:
the `Õ(·)` bounds are `C · (·) · L^c` with `L = log(2+d) + log(2+1/ξ)` (Def. 1.11; p.169: "the
dependence on `ϵ` is polylogarithmic"), and the QRAM size is `Õ(d² p)` = `C d² (p+1) L^c`
rather than `O(d²p)`: the word size of the data structure must grow like `log(1/ξ)` to reach
error `ξ` (the same correction as for Cor. 5.45, on which the proof rests). `Õ(q)` auxiliary
qubits is `C (q+1) L^c`.

Why. The printed claim has no cost model for classical arithmetic, does not say in which
parameters `p` is polylogarithmic, and claims `Õ(1)` gates for an unspecified `ξ` without saying
how they depend on `ξ`; the `O(d²p)` QRAM size with fixed word size `p` cannot reach an
arbitrary `ξ`.

Model. The circuit acts on `w` auxiliary qubits followed by the `q` system qubits, over two-qubit
gates ("additional gates", Rem. 5.44), and calls the QRAM (address `b` qubits, words of `r`
bits) uncontrolled, possibly as its inverse. The block-encoding is the frozen `IsBlockEncoding`
(Def. 7.11, auxiliary register first) with `α = ‖A‖_F` (`frobNorm`, Def. 7.28) and error `ξ`; `A`
is read on qubits through the most-significant-bit-first index map `bitsEquivFin`. -/
theorem blockEncoding_qram :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (q p : ℕ) (ξ : ℝ), 0 < ξ →
      (p : ℝ) ≤ C₀ * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c₀ →
      ∃ (w b r : ℕ) (Prog : List ArithOp) (addr : Qubits b → ℕ)
        (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => b + r) (w + q)),
        (2 : ℝ) ^ b * r ≤ C * ((2 : ℝ) ^ q) ^ 2 * ((p : ℝ) + 1) *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (Prog.length : ℝ) ≤ C * ((2 : ℝ) ^ q) ^ 2 *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (circ.queryCount 0 : ℝ) ≤ C * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (circ.gateCount : ℝ) ≤ C * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (w : ℝ) ≤ C * ((q : ℝ) + 1) * (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ξ)) ^ c ∧
        (∀ s ∈ circ, match s with
          | OracleStep.query _ _ ctrl _ _ => ctrl = none
          | OracleStep.gate _ => True) ∧
        ∀ A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ,
          (∀ i j, |(A i j).re| ≤ (2 : ℝ) ^ p ∧ |(A i j).im| ≤ (2 : ℝ) ^ p) →
          IsBlockEncoding (0 : Qubits w)
            ((circ.unitary fun _ => qramOp b r (qramMatrixWords b r Prog addr A)).submatrix
              (qubitsAppendEquiv w q).symm (qubitsAppendEquiv w q).symm)
            (frobNorm (A.submatrix (bitsEquivFin q) (bitsEquivFin q))) ξ
            (A.submatrix (bitsEquivFin q) (bitsEquivFin q)) := by
  sorry

end QAlgorithms.Nannicini
