import QAlgorithms.Defs.SDP

/-!
# Nannicini, Chapter 8 (part b): the MaxCut SDP relaxation by inexact mirror descent

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §8.4.2–8.4.3: Proposition 8.28 (p.201), Lemma 8.29 (p.201), Theorem 8.30 (p.202),
Lemma 8.33 (p.204), and Proposition 8.34 (p.204) as a corrected statement in a hybrid
classical–quantum QRAM cost model defined below.

Standing assumptions (§8.4, pp.198–200). `C ∈ ℝ^{n×n}` is symmetric (p.198), given here as a real
matrix `C` with `C.IsSymm` and used through its complex image `C.map (↑)`; `Ĉ = C/‖C‖_F` is the
frozen `SDP.cHat` and needs `C ≠ 0`. The binary-search guess is `γ ∈ [−1, 1]` (p.199) and the
precision is `ϵ > 0`. The function `f_γ(ρ) = max{γ − Tr(Ĉρ), Σ_j |ρ_jj − 1/n|}` of Eq. (8.26) is the
frozen `SDP.maxCutF`. The estimate-driven subgradient of pp.200–201 is the frozen
`SDP.maxCutSubgrad`, fed with estimates `estC` of `Tr(Ĉρ)` and `estD j` of `ρ_jj` satisfying
Eq. (8.27). Subgradients and `ϵ`-subgradients (Def. 5.24, p.120) are the frozen `IsEpsSubgradOn`;
the vector space is the real space of Hermitian matrices (Rem. 8.6, 8.9: subgradient steps are taken
in the space of Hermitian matrices), and the dual pairing is the trace inner product
`⟨G, X⟩ = Tr(G X†)` (frozen `traceRePairing`). The iterates of Alg. 6 (p.183) are the frozen
`mmwuIterate`: `ρ^(t) = exp(−η Σ_{τ<t} G^(τ)) / Tr(⋯)`, `ρ^(1) = I/n`. `log` is base 2 (p.11).
-/

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP

/-- Nannicini p.201, Proposition 8.28, **corrected** (trap 30). As printed: "Let `G^(t)` be
computed according to the algorithm above. Then `G^(t) ∈ ∂_{ϵ/2} f_γ(ρ^(t))`."

The zero branch is false as printed: the book's proof only shows that `0` is an `ϵ`-subgradient
(not an `ϵ/2`-subgradient) there. Counterexample: `n = 2`, `γ = −1`,
`ρ = diag(1/2 + ϵ/2, 1/2 − ϵ/2)`, diagonal estimates `1/2 ± 3ϵ/8` and the exact value of
`Tr(Ĉρ)`; the estimated maximum is `3ϵ/4`, so `G = 0`, while `f_γ(ρ) = ϵ` and `f_γ(I/2) = 0`.
The book itself says (p.201) that the zero branch only signals `f_γ(ρ^(t)) ≤ ϵ`. Stated:

1. if the estimated maximum is at most `3ϵ/4`, then `G = 0` and `f_γ(ρ) ≤ ϵ`;
2. otherwise `G ∈ ∂_{ϵ/2} f_γ(ρ)`, the `ϵ/2`-subgradient inequality holding at every Hermitian
   matrix.

The current iterate `ρ^(t)` is any density matrix `ρ`; the estimates satisfy Eq. (8.27). -/
theorem maxCutSubgrad_mem_epsSubdiff {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDensityMatrix ρ) (estC : ℝ) (estD : Fin n → ℝ)
    (hestC : |estC - (cHat (C.map ((↑) : ℝ → ℂ)) * ρ).trace.re| ≤ ε * 4⁻¹)
    (hestD : ∑ j, |estD j - (ρ j j).re| ≤ ε * 4⁻¹) :
    (max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹ →
        maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD = 0 ∧
          maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρ ≤ ε) ∧
      (3 * ε * 4⁻¹ < max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) →
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) ρ
          (traceRePairing (maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε estC estD))) := by
  sorry

/-- Nannicini p.201, Lemma 8.29. Let `h_1, …, h_m` be 1-Lipschitz convex functions and
`f(x) = max_i h_i(x)`. For points `x̄, x̂` with `‖x̄ − x̂‖ ≤ ϵ/4`, let `j ∈ argmax_i h_i(x̂)`. Then,
for `g ∈ ∂h_j(x̂)`, we have `g ∈ ∂_{ϵ̂} f(x̄)`, where `ϵ̂ = (ϵ/4)(‖g‖_* + 1)`.

The space is any real normed space `E` (in Prop. 8.28 it is the space of Hermitian matrices with
the trace norm). Subgradients are elements of the dual `E*` (Def. 5.24), here continuous linear
functionals, and the dual norm `‖g‖_* = max_{‖x‖=1} ⟨g, x⟩` (Def. 8.4, p.181) is the operator norm
of `g`. The index `j` is in the argmax: `h_i(x̂) ≤ h_j(x̂)` for all `i`; the maximum over the
(nonempty, since `j` exists) index set is `Finset.sup'`. -/
theorem epsSubgrad_of_subgrad_active_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (h : Fin m → E → ℝ) (hLip : ∀ i, LipschitzWith 1 (h i))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (h i)) (ε : ℝ) (xbar xhat : E)
    (hdist : ‖xbar - xhat‖ ≤ ε * 4⁻¹) (j : Fin m) (hj : ∀ i, h i xhat ≤ h j xhat)
    (g : E →L[ℝ] ℝ) (hg : IsEpsSubgradOn Set.univ (h j) 0 xhat g.toLinearMap) :
    IsEpsSubgradOn Set.univ
      (fun x => Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ fun i => h i x)
      (ε * 4⁻¹ * (‖g‖ + 1)) xbar g.toLinearMap := by
  sorry

/-- Nannicini p.202, Theorem 8.30 (Convergence of mirror descent for MaxCut SDP). Suppose there
exists `ρ* ∈ S^n_{+,1}` such that `f_γ(ρ*) = 0`. Then the mirror descent algorithm Alg. 6 with step
size `η = ϵ/16`, inexact subgradients `G^(t) ∈ ∂_{ϵ/2} f_γ(ρ^(t))`, and number of steps
`T = (64/ϵ²) log n`, returns density matrices `ρ^(1), …, ρ^(T)` such that
`f_γ((1/T) Σ_{t=1}^T ρ^(t)) ≤ ϵ`.

Alg. 6 obtains `G^(t)` for `t = 1, …, T − 1` and returns `ρ^(1), …, ρ^(T)`, `ρ^(t)` being
`mmwuIterate η G t`; each `G^(t)` is a Hermitian matrix (an element of the dual of the space of
Hermitian matrices) and an `ϵ/2`-subgradient of `f_γ` at `ρ^(t)` over all Hermitian matrices.
Two recorded adjustments: `T = ⌈(64/ϵ²) log₂ n⌉` (the printed `T` need not be an integer; the
ceiling only enlarges it), and `n ≥ 2` (at `n = 1`, `log n = 0` gives `T = 0` and the average of
no iterates is `0`, with `f_γ(0) = max(γ, 1) > ϵ` for `ϵ < 1`). -/
theorem mirrorDescent_maxCut_converges {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (hfeas : ∃ ρs : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix ρs ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ ρs = 0)
    (G : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hG : ∀ t, 1 ≤ t → t < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      (G t).IsHermitian ∧
        IsEpsSubgradOn {X : Matrix (Fin n) (Fin n) ℂ | X.IsHermitian}
          (maxCutF (C.map ((↑) : ℝ → ℂ)) γ) (ε * 2⁻¹) (mmwuIterate (ε * 16⁻¹) G t)
          (traceRePairing (G t))) :
    (∀ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊,
        IsDensityMatrix (mmwuIterate (ε * 16⁻¹) G t)) ∧
      maxCutF (C.map ((↑) : ℝ → ℂ)) γ
        (((⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ : ℕ) : ℂ)⁻¹ •
          ∑ t ∈ Finset.Icc 1 ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊, mmwuIterate (ε * 16⁻¹) G t) ≤ ε := by
  sorry

/-- Nannicini p.204, Lemma 8.33. For every iteration `t` of Alg. 6 applied to (MaxCutSDP-F) as
described in Sect. 8.4.2, `H^(t) = y_1 Ĉ + y_2 D` for some vector `y ∈ ℝ²`, where `D` is a
diagonal matrix. Furthermore, `‖y‖_1 ≤ (4/ϵ) log n`.

The run of §8.4.2: `η = ϵ/16`, `T = ⌈(64/ϵ²) log₂ n⌉` (ceiling as in Theorem 8.30), and for
`τ = 1, …, T − 1` the subgradient `G^(τ)` is the estimate-driven matrix `maxCutSubgrad`
computed from estimates `estC τ`, `estD τ` of `Tr(Ĉρ^(τ))`, `ρ^(τ)_jj` satisfying Eq. (8.27), with
`ρ^(τ) = mmwuIterate η G τ`. The Hamiltonian is `H^(t) = −η Σ_{τ<t} G^(τ)` (Prop. 8.7, Alg. 6), for
`t = 1, …, T`. The normalization `|D_jj| ≤ 1` (proof, p.204: "we can keep `D` normalized so that its
entries are less than 1 in absolute value") is part of the conclusion: without it the bound on
`‖y‖_1` says nothing. -/
theorem maxCut_hamiltonian_structure {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (hC0 : C ≠ 0) (γ : ℝ) (hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (estC : ℕ → ℝ) (estD : ℕ → Fin n → ℝ)
    (hest : ∀ τ, 1 ≤ τ → τ < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      |estC τ - (cHat (C.map ((↑) : ℝ → ℂ)) *
          mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ).trace.re|
          ≤ ε * 4⁻¹ ∧
        ∑ j, |estD τ j - (mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ j j).re|
          ≤ ε * 4⁻¹)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊) :
    ∃ (y : Fin 2 → ℝ) (d : Fin n → ℂ), (∀ j, ‖d j‖ ≤ 1) ∧
      -((ε * 16⁻¹ : ℝ) : ℂ) • ∑ τ ∈ Finset.Ico 1 t,
          maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC τ) (estD τ) =
        ((y 0 : ℝ) : ℂ) • cHat (C.map ((↑) : ℝ → ℂ)) + ((y 1 : ℝ) : ℂ) • Matrix.diagonal d ∧
      |y 0| + |y 1| ≤ 4 * ε⁻¹ * Real.logb 2 n := by
  sorry

/-- Nannicini p.128, Definition 5.39 (QRAM), for the statement of Prop. 8.34 (chunk-local copy of
the QRAM of the Prop. 7.29 and Cor. 5.45 chunks, which a chunk may not import): for stored words
`M_j ∈ {0,1}^r`, `U_QRAM |j⟩|y⟩ = |j⟩|y ⊕ M_j⟩` for all addresses `j ∈ {0,1}^b`, `y ∈ {0,1}^r`.
Address register first. Its size in the sense of Def. 5.39 is `2^b · r`. -/
noncomputable def mcQram (b r : ℕ) (M : Qubits b → Qubits r) :
    Matrix (Qubits (b + r)) (Qubits (b + r)) ℂ :=
  Matrix.reindex (qubitsAppendEquiv b r).symm (qubitsAppendEquiv b r).symm (xorOracle M)

/-- One classical arithmetic operation of the preprocessing that reads the input `C` (chunk-local
copy of the straight-line real-arithmetic model of the Prop. 7.29 chunk, p.168: the "`Õ(n²)`
classical operations" of Prop. 8.34 are, by its proof, those of Prop. 7.29 preparing the QRAM data
structures for `Ĉ`). Each instruction reads earlier values by index and appends one value; each
counts as one operation: `+, −, ×, ÷, √, arccos`, the argument of a complex number, and rational
constants. -/
inductive MCPrepOp where
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
noncomputable def MCPrepOp.value (vals : List ℝ) : MCPrepOp → ℝ
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
noncomputable def mcPrepExec (Prog : List MCPrepOp) (input : List ℝ) : List ℝ :=
  Prog.foldl (fun vals g => vals ++ [g.value vals]) input

/-- The classical description of the real matrix `C ∈ ℝ^{n×n}` given to the preprocessing: its
entries row by row, `C_00, C_01, …`. -/
def mcInput {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  (List.ofFn fun i => List.ofFn fun j => C i j).flatten

/-- The input part of the QRAM, written classically by the preprocessing (Rem. 5.40): word `j` is
the `r`-bit binary expansion (most significant bit first) of the integer part of the program value
with index `addr j`. This is the only way the input `C` reaches the rest of the algorithm. -/
noncomputable def mcStaticWords (b r : ℕ) (Prog : List MCPrepOp) (addr : Qubits b → ℕ) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) : Qubits b → Qubits r :=
  fun j => natToBits r ⌊(mcPrepExec Prog (mcInput C)).getD (addr j) 0⌋₊

/-- The QRAM of Prop. 8.34 holds two halves (address bit `0` selects): the input half `stat`,
written once by the preprocessing from `C` (the data structure for `Ĉ`, Prop. 7.29), and the work
half `dyn`, rewritten by the classical controller between quantum runs (the diagonal matrix `D` of
Lem. 8.33, "stored in QRAM and queried at unit cost", p.204). -/
def mcSplitWords (b r : ℕ) (stat dyn : Qubits b → Qubits r) : Qubits (b + 1) → Qubits r :=
  fun j => if j 0 then dyn (Fin.tail j) else stat (Fin.tail j)

/-- The state before measurement of one quantum run of the hybrid algorithm: the circuit, over
two-qubit gates ("additional gates") and calls to the QRAM (any orientation, possibly controlled),
applied to `|0⟩` on `m` qubits. -/
noncomputable def mcRoundState {m b r : ℕ}
    (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (stat dyn : Qubits b → Qubits r) : EuclideanSpace ℂ (Qubits m) :=
  act (circ.unitary fun _ => mcQram (b + 1) r (mcSplitWords b r stat dyn)) (zeroKet m)

/-- The probability of the measurement record `h` (outcome `h k` of the full computational-basis
measurement in run `k`) of a hybrid algorithm with `R` runs. The circuit and the work-QRAM
contents of run `k` are chosen by the classical controller from the outcomes of runs `0, …, k−1`
only. -/
noncomputable def mcHistProb {m b r R : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r) (stat : Qubits b → Qubits r)
    (h : Fin R → Qubits m) : ℝ :=
  ∏ k : Fin R, prob (mcRoundState (circ k fun i => h ⟨i, i.isLt.trans k.isLt⟩) stat
    (dyn k fun i => h ⟨i, i.isLt.trans k.isLt⟩)) (h k)

/-- The quantum cost along the measurement record `h`: the total number of QRAM accesses plus
additional gates of the `R` circuits actually run. -/
def mcHistCost {m b r R : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (h : Fin R → Qubits m) : ℕ :=
  ∑ k : Fin R, ((circ k fun i => h ⟨i, i.isLt.trans k.isLt⟩).queryCount 0 +
    (circ k fun i => h ⟨i, i.isLt.trans k.isLt⟩).gateCount)

/-- The probability that the measurement record satisfies `Good`. -/
noncomputable def mcSuccessProb {m b r R : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r) (stat : Qubits b → Qubits r)
    (Good : (Fin R → Qubits m) → Prop) : ℝ :=
  open Classical in
  ∑ h : Fin R → Qubits m, if Good h then mcHistProb circ dyn stat h else 0

/-- The solution "determined" by the algorithm, in the source's representation (Rem. 8.27,
p.200: the iterates are kept classically as Hamiltonians, never as explicit matrices; Lem. 8.33,
p.204: `H = y_1 Ĉ + y_2 D` with `D` diagonal): a list of pairs `(y, d)` stands for the average of
the Gibbs states `exp(y_1 Ĉ + y_2 diag(d)) / Tr(⋯)` (Def. 7.34, frozen `gibbsState`), `Ĉ` being the
true normalized input. The empty list stands for the zero matrix, which is not a solution. -/
noncomputable def mcGibbsMixture {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (L : List ((Fin 2 → ℝ) × (Fin n → ℝ))) : Matrix (Fin n) (Fin n) ℂ :=
  ((L.length : ℂ))⁻¹ • (L.map fun p => gibbsState (((p.1 0 : ℝ) : ℂ) • cHat (C.map ((↑) : ℝ → ℂ)) +
    ((p.1 1 : ℝ) : ℂ) • Matrix.diagonal fun j => ((p.2 j : ℝ) : ℂ))).sum

/-- A solution of (MaxCutSDP) (p.199) with optimality and feasibility tolerance `ϵ`: a density
matrix `ρ` (the constraints `Tr ρ = 1`, `ρ ⪰ 0` are kept exactly, p.200) whose diagonal is within
`ϵ` of `(1/n)𝟙` in `ℓ₁` (the norm of `f_γ`, Eq. (8.26)) and whose objective `Tr(Ĉρ)` is within `ϵ`
of the optimum, i.e. of `Tr(Ĉσ)` for every feasible `σ` (density matrix with `diag(σ) = (1/n)𝟙`). -/
def IsMaxCutSDPSolution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsDensityMatrix ρ ∧ ∑ j, |(ρ j j).re - (n : ℝ)⁻¹| ≤ ε ∧
    ∀ σ : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix σ → (∀ j, σ j j = ((n : ℂ))⁻¹) →
      (cHat (C.map ((↑) : ℝ → ℂ)) * σ).trace.re - ε ≤ (cHat (C.map ((↑) : ℝ → ℂ)) * ρ).trace.re

example {m b r : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r) (stat : Qubits b → Qubits r)
    (h : Fin 0 → Qubits m) : mcHistProb circ dyn stat h = 1 := by
  simp [mcHistProb]

example (b r : ℕ) (stat dyn : Qubits b → Qubits r) (j : Qubits b) :
    mcSplitWords b r stat dyn (Fin.cons false j) = stat j := by
  simp [mcSplitWords]

/-- Corrected statement. Nannicini p.204, Proposition 8.34, as printed: "Given access to a QRAM
of size `Õ(n²)`, we can determine a solution to (MaxCutSDP) with optimality and feasibility
tolerance `ϵ` (i.e., problem (MaxCutSDP-F)) using `Õ(n^{1.5}/ϵ⁵)` accesses to the QRAM and
additional gates, and `Õ(n²)` classical operations."

What was changed. (1) Cost model (the source has none): a hybrid algorithm, fixed before the
input `C`, consists of a classical preprocessing program `Prog` (straight-line real arithmetic,
`MCPrepOp`) that alone reads `C` and writes the input half of the QRAM, and `R` quantum runs. Run
`k` applies a circuit over two-qubit gates and QRAM calls to `|0⟩` and measures every qubit (the
QRAM holds words of `r = Õ(1)` bits, the `Õ(1)`-bit entries of the Prop. 7.29 data structure: a
unit-cost call reading an `n²`-bit word would let one access read all of `C`); the
circuit and the work half of the QRAM (where `D` is stored) are chosen by a classical controller
from the earlier outcomes only, and the output is a function of all outcomes. "Accesses to the QRAM
and additional gates" is the total number of QRAM calls plus gates along the run, bounded for
every measurement record; "classical operations" is the length of `Prog`. The controller's own
bookkeeping (tallying samples, forming `G^(t)`, updating `y` and `D`) is not counted, as in the
proof, which inherits the classical cost from Prop. 7.29 alone. (2) Success probability: the
source's estimates hold only with high probability; the output is correct with probability
`≥ 1 − δ` for every `δ ∈ (0, 1)`, and `Õ` may hide `polylog(1/δ)`. (3) "Optimality and
feasibility tolerance `ϵ`" is the reading Rem. 8.36 relies on (a solution of (MaxCutSDP)): a
density matrix with `‖diag(ρ) − 𝟙/n‖₁ ≤ ϵ` and `Tr(Ĉρ) ≥ OPT − ϵ` (`IsMaxCutSDPSolution`), so the
`O(log 1/ϵ)` binary-search calls are inside the algorithm and the `Õ`. The other reading, solving
one (MaxCutSDP-F) instance at a given `γ`, is not stated. (4) "Determine a solution": the output is
the source's classical representation of the iterate, a list of `(y, d)` standing for the average
of the Gibbs states of `y_1 Ĉ + y_2 diag(d)` (`mcGibbsMixture`); without a fixed representation any
decoder could compute the optimum from `Ĉ` itself. (5) `n = 2^q`, the case of the components
Props. 7.29, 7.38 (stated for `d = 2^q`, `n = 2^q`), and `ϵ ≤ 1`. (6) `Õ(g)` is `K · g · L^c` with
`L = log(2+n) + log(2+1/ϵ) + log(2+1/δ)` and absolute `K, c` chosen before `q, ϵ, δ` (Def. 1.11).

Why. The printed claim composes components (Props. 7.21, 7.29, 7.38) whose resources are unpinned
as printed, has no cost model for "classical operations", never states the success probability of
"determine", and does not say what tolerance the binary search over `γ` delivers. Without the
word-length bound a single unit-cost QRAM access could read all of `Ĉ`. The standing
assumptions of §8.4 are kept: `C` real symmetric and nonzero (so `Ĉ = C/‖C‖_F` is defined). -/
theorem maxCutSDP_quantum_complexity :
    ∃ K : ℝ, 0 < K ∧ ∃ c : ℕ, ∀ (q : ℕ) (ε δ : ℝ), 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∃ (b r m R : ℕ) (Prog : List MCPrepOp) (addr : Qubits b → ℕ)
        (circ : (k : ℕ) → (Fin k → Qubits m) →
          OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
        (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r)
        (out : (Fin R → Qubits m) → List ((Fin 2 → ℝ) × (Fin (2 ^ q) → ℝ))),
        (2 : ℝ) ^ (b + 1) * r ≤ K * ((2 : ℝ) ^ q) ^ 2 *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
        (r : ℝ) ≤ K *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
        (Prog.length : ℝ) ≤ K * ((2 : ℝ) ^ q) ^ 2 *
          (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
        (∀ h : Fin R → Qubits m, (mcHistCost circ h : ℝ) ≤
          K * ((2 : ℝ) ^ q * Real.sqrt ((2 : ℝ) ^ q)) / ε ^ 5 *
            (Real.log (2 + (2 : ℝ) ^ q) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c) ∧
        ∀ C : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ, C.IsSymm → C ≠ 0 →
          1 - δ ≤ mcSuccessProb circ dyn (mcStaticWords b r Prog addr C)
            (fun h => IsMaxCutSDPSolution C ε (mcGibbsMixture C (out h))) := by
  sorry

end QAlgorithms.Nannicini
