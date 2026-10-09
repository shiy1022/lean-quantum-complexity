import QAlgorithms.Defs.AmplitudeEstimation

/-!
# Nannicini, Chapter 4 (part c): searching when the number of marked items is not known

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Lemma 4.28 (p.92), Theorem 4.29 (p.93), Corollary 4.30 (p.94), and Theorem 4.31
(quantum minimum finding, p.96) in a corrected form with an explicit bit width, interruption rule
and gate-cost model (see its docstring).

Setting of §4.3.6 (p.91): the setting of §4.2 with `S = H^{⊗n}` (Rem. 4.13) and the phase
reflection `R|j⟩ = (−1)^{f(j)}|j⟩` built from `U_f : |j⟩|y⟩ ↦ |j⟩|y ⊕ f(j)⟩` (p.69), so that
`S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩` with `sin θ = √(|M|/2^n)`, `M = {j : f(j) = 1}`; this `θ` is
the frozen `groverAngle |M| 2^n`. The output states of the amplitude estimation circuit
(Fig. 4.9) on the eigenstates `|ϕ±⟩` are `|ϑ±⟩ = Q_m† (2^{−m/2} Σ_k e^{±2iθk}|k⟩)` (p.92), the
frozen `aeVartheta m (±θ)`. Algorithm 1 (p.94) is the frozen `searchAlg1Weight f` (joint law of
the output, `none` = "no solution", and of the number of applications of `U_f`), with expected
cost `searchAlg1ExpectedCost f`: a round with `m` qubits of precision costs `2^m − 1`
applications of the Grover operator (one `U_f` each) plus one test of `f(j)`, and the final
enumeration costs one application per string tested.
-/

namespace QAlgorithms.Nannicini

open scoped ENNReal

/-- Nannicini p.92–93, Lemma 4.28, in the explicit form its proof derives (p.93):
for `θ ∈ (0, π/2)` (standing assumption of §4.3.6, p.91) and any number `m` of qubits of the
first register, the phase-estimation output states `|ϑ±⟩ = Q_m† (2^{−m/2} Σ_k e^{±2iθk}|k⟩)`
satisfy `|⟨ϑ−|ϑ+⟩| ≤ 1/(2^m sin 2θ)`.

The printed conclusion `|⟨ϑ−|ϑ+⟩| = O(1/(2^m θ))` is false with a constant uniform in `θ`
(for `θ = π/2 − η` with `4η2^m ≪ 1` the overlap is close to `1`), and is only `O(1/2^m)` for
fixed `θ`; the explicit bound, which the proof states right before the `O`-form, is formalized
instead (trap 30; recorded in the chunk's `HARD.md`). -/
theorem aeVartheta_overlap_le (m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ‖inner ℂ (aeVartheta m (-θ)) (aeVartheta m θ)‖ ≤ 1 / ((2 : ℝ) ^ m * Real.sin (2 * θ)) := by
  sorry

/-- Nannicini p.93, Theorem 4.29 (Quantum search; Boyer et al. 1998, Brassard et al. 2002):
there is a constant `C > 0` such that for every `n` and every `f : {0,1}^n → {0,1}`, with
`θ = arcsin √(|M|/2^n)` (`M = {j : f(j) = 1}`), Algorithm 1 (p.94) satisfies:
1. if `θ > 0`, it returns, with probability one, a value `j` with `f(j) = 1`, and the expected
   number of applications of `U_f` is at most `C/θ`;
2. if `θ = 0`, it returns "no solution" (with probability one) and every run uses at most
   `C · 2^n` applications of `U_f`. -/
theorem quantumSearch_unknownCount :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      (0 < groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C / groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n))) ∧
      (groverAngle (Finset.univ.filter fun j => f j = true).card (2 ^ n) = 0 →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        ∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          oc.1 = none ∧ (oc.2 : ℝ) ≤ C * 2 ^ n) := by
  sorry

/-- Nannicini p.94, Corollary 4.30: there is a constant `C > 0` such that for every `n` and every
Boolean function `f : {0,1}^n → {0,1}` with a nonempty set `M = {j : f(j) = 1}` of marked
elements, Algorithm 1 (whose input is only the oracle `U_f`, not `|M|`) returns an element of `M`
with probability one, using at most `C √(2^n/|M|)` applications of `U_f` in expectation. -/
theorem quantumSearch_unknownCount_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      1 ≤ (Finset.univ.filter fun j => f j = true).card →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C * Real.sqrt ((2 : ℝ) ^ n /
            ((Finset.univ.filter fun j => f j = true).card : ℝ))) := by
  sorry

/-- Quantum minimum finding (§4.4.1, Algorithm 2 and Theorem 4.31, pp.95–97).

Cost model (chunk-local; the source fixes none). `f : {0,1}^n → ℤ` takes values of bit width `b`
(`|f(j)| < 2^b`), and `U_f` writes `f(j)` in binary (p.95). Every application of the marking
unitary `U_m : |j⟩|y⟩ ↦ |j⟩|y ⊕ I(f(j) < f(ℓ))⟩` (Alg. 2, line 3) counts as one application of
`U_f`, as in the proof (p.97: "a single call to `U_f` plus some binary arithmetic operations"),
and is charged `mfStepGates n b = 3n + 2b + 1` additional gates: `S = H^{⊗n}`, `S†` and the
reflection `F` about `|0⟩` at `n` gates each, a `b`-bit comparison with `f(ℓ)` and its
uncomputation at `b` gates each, and one gate of control overhead. A round of Alg. 1 with `m`
qubits of precision is moreover charged `m + m(m+1)/2` gates (the `m` Hadamards and the inverse
QFT `Q_m†`: `m` Hadamards and `m(m−1)/2` controlled rotations). Only the asymptotic form of these
counts (`Θ(n + b)` per query, `Θ(m²)` per round) matters for the theorem.

This definition: gates charged, besides the call to `U_f`, for one application of the marking
unitary `U_m` of Alg. 2 inside a Grover iterate `S F S† R` (or for one test of a string):
`3n + 2b + 1` (Nannicini p.94–97). -/
def mfStepGates (n b : ℕ) : ℕ :=
  3 * n + 2 * b + 1

/-- Fixed gate overhead of one round of Alg. 1 (p.94) with `m` qubits of precision: `m`
Hadamards on the first register and the inverse QFT `Q_m†` counted as `m(m+1)/2` gates. -/
def mfRoundOverhead (m : ℕ) : ℕ :=
  m + m * (m + 1) / 2

/-- The precisions of the rounds of Alg. 1 (p.94): `m = 1, 1, 2, 2, …, n−1, n−1` (two rounds for
each `m < n`); this is the list used by the frozen `searchAlg1Weight`. -/
def alg1RoundList (n : ℕ) : List ℕ :=
  (List.range (n - 1)).flatMap fun i => [i + 1, i + 1]

/-- Additional gates performed by Alg. 1 (p.94) by the time it has made `c` applications of the
marking unitary, when its remaining rounds have precisions `rounds`. A round with `m` qubits
makes `2^m` applications (`2^m − 1` Grover iterates and one test of the measured string, as in
the frozen `searchAlg1Rounds`); a round that is entered is charged its full overhead
`mfRoundOverhead m`; after the rounds, every enumerated string costs one application. Since the
round costs are fixed, the number `c` of applications made so far determines the position in the
run, so this is both the gate count of a completed call of cost `c` and of a call interrupted
after `c` applications. -/
def alg1Gates (n b : ℕ) : List ℕ → ℕ → ℕ
  | _, 0 => 0
  | [], c => c * mfStepGates n b
  | m :: rest, c =>
      if c ≤ 2 ^ m then mfRoundOverhead m + c * mfStepGates n b
      else mfRoundOverhead m + 2 ^ m * mfStepGates n b + alg1Gates n b rest (c - 2 ^ m)

/-- The main loop of Alg. 2 (Nannicini p.96) with budget `T` applications of `U_f`, as a
weight on final triples `(ℓ, applications of U_f, additional gates)`. Arguments: remaining
fuel, incumbent `ℓ`, applications `q` and gates `g` used so far, and the outcome.

Each iteration runs Alg. 1 (the frozen `searchAlg1Weight`) with the marking function
`j ↦ I(f(j) < f(ℓ))`, whose outcome `(k, c)` (returned index or "no solution", applications of
the marking unitary) has the frozen weight. If the call completes within the budget
(`q + c ≤ T`), the incumbent becomes `k` when `f(k) < f(ℓ)` (line 5, charged `mfStepGates n b`
gates) and the loop continues. Otherwise the call is **interrupted** as soon as the `T`-th
application of `U_f` has been made (the reading of "while the number of evaluations of `U_f` does
not exceed `T`" that the `O(√2^n log 1/δ)` total needs), its result is discarded and Alg. 2
returns `ℓ`, having used exactly `T` applications and `alg1Gates … (T − q)` gates for that call.
Every call makes at least one application, so fuel `T + 1` reaches an interruption on every
path; the fuel-`0` clause is never reached from `minFindWeight`. -/
noncomputable def minFindLoop {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ) :
    ℕ → Qubits n → ℕ → ℕ → Qubits n × ℕ × ℕ → ℝ≥0∞
  | 0, l, q, g, out => if out = (l, q, g) then 1 else 0
  | fuel + 1, l, q, g, out =>
      ∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight (fun j => decide (f j < f l)) oc *
        (if q + oc.2 ≤ T then
          minFindLoop f b T fuel
            (match oc.1 with
              | some k => if f k < f l then k else l
              | none => l)
            (q + oc.2) (g + alg1Gates n b (alg1RoundList n) oc.2 + mfStepGates n b) out
        else if out = (l, T, g + alg1Gates n b (alg1RoundList n) (T - q)) then 1 else 0)

/-- One run of Alg. 2 (Nannicini p.96) with budget `T`: the initial incumbent `ℓ` is uniform on
`{0,1}^n` (line 1); weight of the final triple `(returned ℓ, applications of U_f, additional
gates)`. -/
noncomputable def minFindWeight {n : ℕ} (f : Qubits n → ℤ) (b T : ℕ)
    (out : Qubits n × ℕ × ℕ) : ℝ≥0∞ :=
  ∑ l : Qubits n, ((2 : ℝ≥0∞) ^ n)⁻¹ * minFindLoop f b T (T + 1) l 0 0 out

/-- Probability of an event `E` about the outcomes of `k` independent runs of Alg. 2 with budget
`T` (the repetition in the proof of Theorem 4.31, p.97). -/
noncomputable def minFindRepeatProb {n : ℕ} (f : Qubits n → ℤ) (b T k : ℕ)
    (E : (Fin k → Qubits n × ℕ × ℕ) → Prop) : ℝ≥0∞ :=
  open Classical in
  ∑' outs : Fin k → Qubits n × ℕ × ℕ, if E outs then ∏ i, minFindWeight f b T (outs i) else 0

/-- Corrected statement. Nannicini p.96, Theorem 4.31 (Quantum minimum finding; Dürr–Høyer).
Printed: for `f : {0,1}^n → ℤ` evaluated in binary by `U_f` and `δ > 0`, Alg. 2 determines the
global minimum of `f` with probability at least `1 − δ` using `O(√2^n log 1/δ)` applications of
`U_f` in total and `Õ(√2^n)` additional gates.

Changed: (1) the bit width `b` of the values of `f` (`|f(j)| < 2^b`) is a named parameter, the
constants are uniform in it, and the gate bound is `C √2^n (n + b + 1)(1 + log 1/δ)` in the cost
model of this section (`mfStepGates`, `mfRoundOverhead`): the factors `n + b + 1` and
`1 + log 1/δ` are the polylogarithmic factors that `Õ` suppresses (Def. 1.11), made explicit;
(2) a call of Alg. 1 that would exceed the budget `T` is interrupted at the `T`-th application of
`U_f` and Alg. 2 then returns its incumbent (`minFindLoop`); (3) the budget and the number of
repetitions are the proof's (p.97): `T = ⌈c √2^n⌉` for an absolute constant `c` (the proof's
`3t̄ = 9c'√2^n`, `c'` the constant of Cor. 4.30), and `k = ⌈log₃ 1/δ⌉` independent runs, the
answer being an `f`-minimal one of the `k` returned indices, which is a global minimizer iff
some returned index is (its selection costs `k` more evaluations, counted); (4) `δ < 1` and
`log 1/δ` read as `1 + log 1/δ`, since at least one evaluation is needed for every `δ < 1`.

Why: each application of `U_m` compares a `b`-bit value with `f(ℓ)` (`Θ(b)` gates) and the source
never fixes `b`, so `Õ(√2^n)` is false when `b` is not polylogarithmic in `2^n` unless `b` is
among the suppressed parameters; and without interruption a call of Alg. 1 with no marked item
(always the case once `ℓ` is the minimum) enumerates all `2^n` strings, so the printed loop
condition alone does not give the `O(√2^n log 1/δ)` total. -/
theorem quantumMinimumFinding :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n b : ℕ) (f : Qubits n → ℤ), (∀ j, |f j| < 2 ^ b) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - δ) ≤
            minFindRepeatProb f b ⌈c * Real.sqrt ((2 : ℝ) ^ n)⌉₊ ⌈Real.logb 3 (1 / δ)⌉₊
              (fun outs => ∃ i, ∀ j, f (outs i).1 ≤ f j) ∧
        ∀ outs : Fin ⌈Real.logb 3 (1 / δ)⌉₊ → Qubits n × ℕ × ℕ,
          (∏ i, minFindWeight f b ⌈c * Real.sqrt ((2 : ℝ) ^ n)⌉₊ (outs i)) ≠ 0 →
            (((∑ i, (outs i).2.1) + ⌈Real.logb 3 (1 / δ)⌉₊ : ℕ) : ℝ) ≤
                C * Real.sqrt ((2 : ℝ) ^ n) * (1 + Real.log (1 / δ)) ∧
            (((∑ i, (outs i).2.2) + ⌈Real.logb 3 (1 / δ)⌉₊ * mfStepGates n b : ℕ) : ℝ) ≤
                C * Real.sqrt ((2 : ℝ) ^ n) * ((n + b + 1 : ℕ) : ℝ) * (1 + Real.log (1 / δ)) := by
  sorry

end QAlgorithms.Nannicini
