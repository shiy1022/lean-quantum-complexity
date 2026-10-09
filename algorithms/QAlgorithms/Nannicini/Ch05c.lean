import QAlgorithms.Defs.GradientMethods

/-!
# Nannicini, Chapter 5 (part c): encoding an arbitrary vector in a quantum state

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §5.2: Proposition 5.36 (p.125) and Corollary 5.37 (p.126); and, as corrected
statements, Theorem 5.33 (p.123, §5.1.4) and Corollary 5.45 (p.130, §5.3.2).

Conventions. The amplitude encoding `|amp(x)⟩ = ∑_j x_j/‖x‖ |j⟩` on `n = ⌈log d⌉` qubits
(Def. 5.34) is `padState n (normalizedVec x)`, the index `j` being read from the qubits most
significant bit first (`bitsToNat`). Algorithm 4 (p.126) is the frozen `alg4Unitary`: the binary
tree values `N(k, j)` are `ampTreeValue`, line 2 and line 5 are the steps `alg4Step n x k`
(`k = 0` is the initialization `|ψ₁⟩`, wire `k` is the fresh qubit of iteration `k`, controlled
by the first `k` wires), and line 7 is the sign diagonal with `sign(x_j) = −1` if `x_j < 0` and
`+1` otherwise.
-/

namespace QAlgorithms.Nannicini

/-- Nannicini p.125, Proposition 5.36: "Alg. 4 returns a quantum circuit on n qubits mapping
`|0⟩` to `|amp(x)⟩`."

Standing assumptions of §5.2 (p.124) and Alg. 4 (p.126): `d = 2^n`, `x ∈ ℝ^d` with `‖x‖ = 1`;
`n ≥ 1` because the initialization (line 2) reads the level-1 nodes `N(1, 0)`, `N(1, 1)` of the
tree. The conclusion: the operator produced by Alg. 4 is unitary (a quantum circuit) and maps
`|0…0⟩` to `|amp(x)⟩`. -/
theorem alg4_prepares_ampEncoding (n : ℕ) (hn : 1 ≤ n) (x : Fin (2 ^ n) → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) :
    alg4Unitary n x ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧
      act (alg4Unitary n x) (zeroKet n) =
        padState n (normalizedVec (WithLp.toLp 2 fun j => (x j : ℂ))) := by
  sorry

/-- Nannicini p.126, Corollary 5.37: "Given a classical description of `x ∈ ℂ^d` in finite
precision, there is a circuit that implements the mapping `|0⟩ → |amp(x)⟩` with error at most
`ϵ` with gate complexity `Õ(d)`."

The circuit is built from the classical data `x` (Rem. 5.35), over the gate set `{H, T, CX}` of
Thm. 1.43, on the `n = ⌈log d⌉` qubits of `|amp(x)⟩` plus `w` ancillas that start in `|0⟩`.
"Error at most `ϵ`" is the Euclidean distance between the produced state and
`|amp(x)⟩ ⊗ |0^w⟩` (§1.3.6). `Õ(d)` with the dependence on `ϵ` polylogarithmic (p.127) is
`C · d · (log(2 + d) + log(2 + 1/ϵ))^c` with constants `C > 0`, `c` chosen before `d`, `x`, `ϵ`.
The statement is for every nonzero `x ∈ ℂ^d`, which contains every finite-precision input. -/
theorem ampEncoding_gateComplexity :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (d : ℕ) (x : Fin d → ℂ), x ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ (w : ℕ) (circ : Circuit htcxGateSet (Nat.clog 2 d + w)),
        (circ.size : ℝ) ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        ‖act circ.unitary (zeroKet (Nat.clog 2 d + w)) -
            WithLp.toLp 2 (fun z : Qubits (Nat.clog 2 d + w) =>
              if ∀ k : Fin w, z (Fin.natAdd (Nat.clog 2 d) k) = false then
                padState (Nat.clog 2 d) (normalizedVec (WithLp.toLp 2 x))
                  (fun i => z (Fin.castAdd w i))
              else 0)‖ ≤ ε := by
  sorry

/-- An oracle-circuit step that is a gate, or a query (possibly the adjoint) that is **not**
controlled by another wire. The QRAM of Def. 5.39 and the membership oracle of Thm. 5.33 are
called as given; the source never grants controlled access. -/
def uncontrolledStep {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} : OracleStep S a n → Prop
  | .gate _ => True
  | .query _ _ c _ _ => c = none

/-- Nannicini p.128, Definition 5.39 (QRAM): for stored words `M_j ∈ {0,1}^q`,
`U_QRAM |j⟩|y⟩ = |j⟩|y ⊕ M_j⟩` for all `j ∈ {0,1}^a`, `y ∈ {0,1}^q`. The address register is the
first `a` qubits, the data register the last `q`; `⊕` is bitwise XOR (the additive group of
`Qubits q`). Its size in the sense of Def. 5.39 is `2^a · q`. The data is a parameter
(Rem. 5.41: a QRAM is a family of unitaries indexed by its contents). -/
noncomputable def qramUnitary (a q : ℕ) (M : Qubits a → Qubits q) :
    Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ :=
  Matrix.reindex (qubitsAppendEquiv a q).symm (qubitsAppendEquiv a q).symm (xorOracle M)

/-- One classical arithmetic operation (cost model for the "Õ(d) classical arithmetic operations"
of Nannicini p.130, Cor. 5.45 and Rem. 5.44, which the source does not define). A program is a
straight-line program over the reals: each instruction reads earlier values by index and appends
one new value. The operations are the ones the preprocessing of p.124 and p.129–130 performs:
the squared moduli `|x_j|²` and subtree sums of the tree of Fig. 5.6, normalization by `‖x‖`,
the rotation angles `2 arccos √(N(k+1,2j)/N(k)…)` and the phases of the complex entries
(Cor. 5.37's proof), plus rational constants for fixed-point scaling. Each counts as one
operation. -/
inductive ArithInstr where
  | const (c : ℚ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | div (i j : ℕ)
  | sqrt (i : ℕ)
  | arccos (i : ℕ)
  | arg (i j : ℕ)

/-- The value an instruction appends, given the values computed so far (an out-of-range index
reads `0`; `t / 0 = 0` as in Lean). `arg i j` is the argument of the complex number
`vals[i] + i·vals[j]`. -/
noncomputable def ArithInstr.value (vals : List ℝ) : ArithInstr → ℝ
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
noncomputable def arithRun (P : List ArithInstr) (input : List ℝ) : List ℝ :=
  P.foldl (fun vals g => vals ++ [g.value vals]) input

/-- The classical description of `x ∈ ℂ^d` given to the preprocessing: the list
`Re x_0, Im x_0, Re x_1, Im x_1, …`. -/
noncomputable def complexInput {d : ℕ} (x : Fin d → ℂ) : List ℝ :=
  (List.ofFn fun j => [(x j).re, (x j).im]).flatten

/-- The QRAM contents written by the classical preprocessing (Rem. 5.40: classical write): word
`j` is the `q`-bit binary expansion (most significant bit first) of the integer part of the
program value with index `addr j`. Storing a value is not counted as an arithmetic operation. -/
noncomputable def qramWords (a q : ℕ) (P : List ArithInstr) (addr : Qubits a → ℕ) {d : ℕ}
    (x : Fin d → ℂ) : Qubits a → Qubits q :=
  fun j => natToBits q ⌊(arithRun P (complexInput x)).getD (addr j) 0⌋₊

/-- Corrected statement. Nannicini p.130, Corollary 5.45, as printed: "Given a classical
description of `x ∈ ℂ^d` in finite precision and a QRAM of size `Õ(d)`, there is a circuit that
implements the mapping `|0⟩ → |amp(x)⟩` with error at most `ϵ` using `O(log d)` QRAM queries,
`O(log² d)` additional gates, and `Õ(d)` classical arithmetic operations to initialize the QRAM
data structure."

What was changed. (1) The gate bound `O(log² d)` is replaced by
`O(log d · (log d + log(1/ϵ)))`, and the QRAM size and the classical cost `Õ(d)` may carry
polylogarithmic factors in `1/ϵ`. This is the source's own count on p.130, `O(n)` queries and
`O(nq)` gates with `n = log d` levels and word size `q`, with `q` allowed to grow like
`log d + log(1/ϵ)`; for `ϵ ≥ 1/poly(d)` it is the printed `O(log² d)`. (2) "Classical arithmetic
operations" are counted in the straight-line real-arithmetic model `ArithInstr` (one operation
per `+, −, ×, ÷, √, arccos, arg` or constant); the QRAM is written classically from the
program's values (`qramWords`).

Why. The printed proof fixes `q = O(log d)` independently of `ϵ` ("this already gives precision
exponential in d"), so its `O(log² d)` gates cannot reach an arbitrary error `ϵ`: fixed-point
words of `O(log d)` bits give error at least about `2^{-q}`. The source gives no cost model for
"classical arithmetic operations".

The model. The circuit runs on the `n = ⌈log d⌉` output qubits plus `w` ancillas that start in
`|0⟩`, over arbitrary two-qubit gates (Rem. 5.44: "additional (two-qubit) gates"), and calls the
QRAM `U_QRAM` of Def. 5.39 (address `a` qubits, words of `q` bits), uncontrolled, possibly as its
inverse. The circuit, the program and the addressing do not depend on `x`: `x` enters only through
the QRAM contents (Rem. 5.41). Error is the Euclidean distance from `|amp(x)⟩ ⊗ |0^w⟩`, as in
Cor. 5.37. The constants `C, c` come before `d`, `x`, `ϵ`. -/
theorem ampEncoding_qram :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε →
      ∃ (a q w : ℕ) (P : List ArithInstr) (addr : Qubits a → ℕ)
        (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (Nat.clog 2 d + w)),
        (2 : ℝ) ^ a * q ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        (P.length : ℝ) ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        (circ.queryCount 0 : ℝ) ≤ C * Real.log (2 + d) ∧
        (circ.gateCount : ℝ) ≤
          C * Real.log (2 + d) * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ∧
        (∀ s ∈ circ, uncontrolledStep s) ∧
        ∀ x : Fin d → ℂ, x ≠ 0 →
          ‖act (circ.unitary fun _ => qramUnitary a q (qramWords a q P addr x))
              (zeroKet (Nat.clog 2 d + w)) -
            WithLp.toLp 2 (fun z : Qubits (Nat.clog 2 d + w) =>
              if ∀ k : Fin w, z (Fin.natAdd (Nat.clog 2 d) k) = false then
                padState (Nat.clog 2 d) (normalizedVec (WithLp.toLp 2 x))
                  (fun i => z (Fin.castAdd w i))
              else 0)‖ ≤ ε := by
  sorry

/-- A unitary implementing `MEM_{0,δ}(K)` in superposition (the object of Nannicini p.123,
Thm. 5.33, which the source does not define). Points are given in an `m`-qubit register through
an encoding `enc` of bit strings as points of `ℝ^d`; the oracle has an answer qubit (the first
qubit of its second register) and `k` workspace qubits, which start in `|0⟩`. On each basis
point `|p⟩` it leaves the point register unchanged and leaves the answer qubit holding the
correct membership answer `[enc p ∈ K]` with probability at least `1 − δ`. With precision `0`,
the two assertions of Def. 5.22 (p.119), `x ∈ B₂(K, 0) = K` and `x ∉ B₂(K, −0) = K`, are exact
membership; `δ` is the failure probability of Def. 5.22. -/
def IsQuantumMembershipOracle {d m k : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (enc : Qubits m → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (O : Matrix (Qubits (m + (k + 1))) (Qubits (m + (k + 1))) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup (Qubits (m + (k + 1))) ℂ ∧
    ∀ p : Qubits m, ∃ φ : EuclideanSpace ℂ (Qubits (k + 1)),
      act O (ket (Fin.append p fun _ => false)) =
          WithLp.toLp 2 (fun z => if (qubitsAppendEquiv m (k + 1) z).1 = p then
            φ (qubitsAppendEquiv m (k + 1) z).2 else 0) ∧
        1 - δ ≤ (open Classical in probEvent φ fun z => (z 0 = true ↔ enc p ∈ K))

/-- Corrected statement. Nannicini p.123, Theorem 5.33, as printed: "Let `K ⊂ ℝ^d` be a convex
set satisfying `B₂(0, r) ⊂ K ⊂ B₂(0, R)` for given `r, R ∈ ℝ`, `0 < r < R`, and let
`x ∉ B(K, −ϵ)`. For any `ϵ, δ ∈ ℝ`, `0 < ϵ < R`, `0 < δ < 1/3`, we can implement `SEP_{ϵ,δ}(x)`
with `Õ(1)` calls to a quantum oracle implementing `MEM_{0,ϵ′}(K)`, for an appropriately chosen
`ϵ′`."

What was changed. (1) "A quantum oracle implementing `MEM_{0,ϵ′}(K)`" is made a definition,
`IsQuantumMembershipOracle` (point register preserved, answer correct with probability
`≥ 1 − ϵ′` on every basis point; adjoint calls allowed, controlled calls not). The algorithm
chooses how points are written in qubits (`enc`); it must work for **every** such oracle, for
every workspace size `k` of the oracle and every admissible `K`. (2) "Appropriately chosen `ϵ′`"
is an existential `ϵ′ > 0` depending only on `d, r, R, ϵ, δ`, chosen before `x`, `K` and the
oracle. An oracle meeting the specification for `ϵ′` meets it for every larger value, so this is
"for every sufficiently accurate oracle". It does not trivialize the claim: the content is the
query count. (3) `Õ(1)` is `C · (log(2+d) + log(2+R) + log(2+1/r) + log(2+1/ϵ) + log(2+1/δ))^c`
with absolute `C, c` (Def. 1.11: polylogarithmic in the suppressed instance parameters).
(4) The returned separating vector must have `‖g‖₂ = 1`. Def. 5.22 as printed lets `g = 0`
satisfy `⟨g, y⟩ ≤ ⟨g, x⟩ + ϵ`, which would make `SEP` answerable with no query at all.

Why. The source leaves `ϵ′`, the quantum oracle model and the parameters hidden in `Õ(1)`
unpinned, and its proof is a sketch through Prop. 5.25 (iii) and Prop. 5.31. The statement
asserts only what the theorem sentence claims, with these choices visible.

Output. The algorithm is a circuit on `n` qubits started in `|0⟩` and measured in the
computational basis; the outcome is decoded by `out` into the assertion `x ∈ B₂(K, ϵ)` (`none`)
or a vector `g` (`some g`). The decoding is fixed before `K` and the oracle. -/
theorem separation_from_quantumMembership :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (d : ℕ) (r R ε δ : ℝ), 0 < r → r < R → 0 < ε → ε < R →
      0 < δ → δ < 1 / 3 →
      ∃ ε' : ℝ, 0 < ε' ∧ ∀ x : EuclideanSpace ℝ (Fin d),
        ∃ (m : ℕ) (enc : Qubits m → EuclideanSpace ℝ (Fin d)), ∀ k : ℕ,
          ∃ (n : ℕ) (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => m + (k + 1)) n)
            (out : Qubits n → Option (EuclideanSpace ℝ (Fin d))),
            (circ.queryCount 0 : ℝ) ≤ C * (Real.log (2 + d) + Real.log (2 + R) +
              Real.log (2 + 1 / r) + Real.log (2 + 1 / ε) + Real.log (2 + 1 / δ)) ^ c ∧
            (∀ s ∈ circ, uncontrolledStep s) ∧
            ∀ K : Set (EuclideanSpace ℝ (Fin d)), Convex ℝ K →
              Metric.closedBall 0 r ⊆ K → K ⊆ Metric.closedBall 0 R →
              x ∉ {y | Metric.closedBall y ε ⊆ K} →
              ∀ O : Matrix (Qubits (m + (k + 1))) (Qubits (m + (k + 1))) ℂ,
                IsQuantumMembershipOracle K enc ε' O →
                1 - δ ≤ (open Classical in
                  probEvent (act (circ.unitary fun _ => O) (zeroKet n)) fun z =>
                    match out z with
                    | none => ∃ y ∈ K, dist x y ≤ ε
                    | some g => ‖g‖ = 1 ∧ ∀ y, Metric.closedBall y ε ⊆ K →
                        inner ℝ g y ≤ inner ℝ g x + ε) := by
  sorry

end QAlgorithms.Nannicini
