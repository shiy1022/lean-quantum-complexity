import QAlgorithms.Defs.Learning

/-!
# A survey of quantum learning theory, §5: Time complexity

S. Arunachalam, R. de Wolf, *A survey of quantum learning theory* (2017), cited "survey p.N"
(PDF pages).

This chunk's only node is Theorem 5.4 (Atıcı–Servedio, survey p.19: learning `k`-juntas under the
uniform distribution with `O(k log(k)/ε)` uniform quantum examples, `O(2^k)` uniform classical
examples and `O(nk log(k)/ε + 2^k log(1/ε))` time). As printed it cannot be stated: the time bound
has no cost model, the confidence is never given, and the classical-example count contradicts the
proof sketch. It is stated here as a corrected theorem, in the explicit cost model of the proof
sketch (the chunk-local definitions below); see the theorem's docstring.

Register layout of the quantum stage (chunk-local): `T` uniform quantum examples of `n + 1` qubits
each, followed by `w` ancillas in `|0⟩`. Example `j` occupies wires `j(n+1), …, j(n+1)+n`: wires
`j(n+1)+i` (`i < n`) hold `x_i`, wire `j(n+1)+n` holds the label `f(x)`.
-/

namespace QAlgorithms.LearningSurvey

/-- A Boolean function on `{0,1}^n` is a `k`-junta if it depends on at most `k` of its `n` input
bits (survey p.19: "functions that depend (possibly non-linearly) on at most `k` of the `n` input
bits"). -/
def IsJunta {n : ℕ} (f : Qubits n → Bool) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ k ∧ ∀ x y : Qubits n, (∀ i ∈ S, x i = y i) → f x = f y

/-- Bit `p` of a computational-basis string, `false` past its end (an index helper). -/
def regBit {N : ℕ} (z : Qubits N) (p : ℕ) : Bool :=
  if h : p < N then z ⟨p, h⟩ else false

/-- The input part `x` of the `j`-th example register (wires `j(n+1), …, j(n+1)+n−1`). -/
def exInput {N : ℕ} (n : ℕ) (z : Qubits N) (j : ℕ) : Qubits n :=
  fun i => regBit z (j * (n + 1) + (i : ℕ))

/-- The label qubit of the `j`-th example register (wire `j(n+1)+n`). -/
def exLabel {N : ℕ} (n : ℕ) (z : Qubits N) (j : ℕ) : Bool :=
  regBit z (j * (n + 1) + n)

/-- `T` uniform quantum examples of `f` followed by `w` ancillas in `|0⟩`: the state
`(∑_x 2^{-n/2} |x, f(x)⟩)^{⊗T} ⊗ |0^w⟩` (survey §3.2, pp.6–7, uniform `D`), in the register
layout of the module docstring. Its amplitude on a basis string is `2^{-nT/2}` if every label
qubit equals `f` of its input part and every ancilla is `0`, and `0` otherwise. -/
noncomputable def juntaExamplesState (n T w : ℕ) (f : Qubits n → Bool) :
    EuclideanSpace ℂ (Qubits (T * (n + 1) + w)) :=
  WithLp.toLp 2 fun z =>
    if (∀ p : Fin (T * (n + 1) + w), T * (n + 1) ≤ (p : ℕ) → z p = false) ∧
        (∀ j : Fin T, exLabel n z j = f (exInput n z j))
    then ((((Real.sqrt 2) ^ n)⁻¹ ^ T : ℝ) : ℂ) else 0

/-- The truth-table hypothesis of the proof sketch (survey p.19): given the variable set `V`
(as an indicator) and classical examples `(x_j, f(x_j))`, the hypothesis on `x` is the label of the
first example agreeing with `x` on `V`, and `false` if no example does. (The source fills unseen
and inconsistent cells "say with random values"; the first-seen label and the fixed value `false`
are such a choice.) -/
def tableHypothesis {n T : ℕ} (V : Fin n → Bool) (xs : Fin T → Qubits n) (f : Qubits n → Bool) :
    Qubits n → Bool :=
  fun x =>
    match (List.finRange T).find? (fun j => decide (∀ i, V i = true → xs j i = x i)) with
    | some j => f (xs j)
    | none => false

/-- A hybrid junta learner in the cost model of the proof sketch of Theorem 5.4 (survey p.19),
fixed here because the source states none:

1. a quantum stage: a circuit `circ` over the gate set `{H, T, CNOT}` acting on `TQ` uniform
   quantum examples and `anc` ancillas, after which every qubit is measured in the computational
   basis;
2. a classical bit-level stage: a well-formed Boolean circuit `post` (AND/OR/NOT gates) mapping the
   measurement outcome to the indicator of a variable set `V ⊆ [n]`;
3. a table stage: `TC` uniform classical examples are read and the hypothesis is
   `tableHypothesis V`.

The time is `cost`: one unit per quantum gate, per measured qubit, per Boolean gate, per classical
example (reading it and writing its label into the table cell indexed by its `V`-bits, a
unit-cost step), and per table cell (`2^{|V|}`, worst case over the outcomes). -/
structure JuntaHybridLearner (n : ℕ) where
  TQ : ℕ
  anc : ℕ
  circ : Circuit htcxGateSet (TQ * (n + 1) + anc)
  post : BoolCircuit (TQ * (n + 1) + anc) n
  post_wf : post.WellFormed
  TC : ℕ

/-- The time of a hybrid junta learner in the cost model of `JuntaHybridLearner`. -/
def JuntaHybridLearner.cost {n : ℕ} (L : JuntaHybridLearner n) : ℕ :=
  L.circ.size + (L.TQ * (n + 1) + L.anc) + L.post.size + L.TC +
    Finset.univ.sup fun z : Qubits (L.TQ * (n + 1) + L.anc) => 2 ^ hammingWeight (L.post.eval z)

/-- The probability that the learner outputs a hypothesis of error at most `ε` under the uniform
distribution on `{0,1}^n`: the quantum stage's outcome `z` has probability
`|⟨z| circ |examples⟩|²`, and the `TC` classical examples are independent and uniform. -/
noncomputable def JuntaHybridLearner.successProb {n : ℕ} (L : JuntaHybridLearner n)
    (f : Qubits n → Bool) (ε : ℝ) : ℝ :=
  ∑ z : Qubits (L.TQ * (n + 1) + L.anc),
    prob (act L.circ.unitary (juntaExamplesState n L.TQ L.anc f)) z *
      ((((2 : ℝ) ^ n) ^ L.TC)⁻¹ * ∑ xs : Fin L.TC → Qubits n,
        if Learning.pacError (Learning.uniformDist (Qubits n)) f
            (tableHypothesis (L.post.eval z) xs f) ≤ ε then (1 : ℝ) else 0)

/-- Corrected statement. Survey p.19, Theorem 5.4 ([AS09]), as printed: "There exists a quantum
algorithm for learning `k`-juntas under the uniform distribution that uses `O(k log(k)/ε)` uniform
quantum examples, `O(2^k)` uniform classical examples, and `O(nk log(k)/ε + 2^k log(1/ε))` time."

Changed: (1) the time is measured in the explicit cost model `JuntaHybridLearner.cost` (quantum
gates from `{H, T, CNOT}`, measured qubits, Boolean gates, one unit per classical example and per
truth-table cell), the model the proof sketch's count uses; (2) the classical-example bound is
`O(2^k log(1/ε))`, as used in the proof sketch, instead of the printed `O(2^k)`; (3) "with high
probability" is read as: for every fixed confidence `1 − δ`, `δ ∈ (0,1)`, with the constant `C`
depending on `δ` only (the bounds carry no `δ`). The `O`-thresholds are `k ≥ 2` and `ε ≤ 1/2`, where
`log k` and `log(1/ε)` are positive.

Why: the source fixes no cost model, and the printed time bound fails in a bit-cost or word-RAM
model (reading the `V`-bits of `2^k log(1/ε)` classical examples alone costs `k 2^k log(1/ε)`); the
confidence is never given; and the printed `O(2^k)` classical examples contradicts the proof
sketch, which needs `O(2^k log(1/ε))` to see `1 − ε/2` of the `2^{|V|}` table cells. -/
theorem juntaLearning_quantum_corrected :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ L : JuntaHybridLearner n,
          (L.TQ : ℝ) ≤ C * ((k : ℝ) * Real.log k / ε) ∧
          (L.TC : ℝ) ≤ C * ((2 : ℝ) ^ k * Real.log (1 / ε)) ∧
          (L.cost : ℝ) ≤ C * ((n : ℝ) * k * Real.log k / ε + (2 : ℝ) ^ k * Real.log (1 / ε)) ∧
          ∀ f : Qubits n → Bool, IsJunta f k → L.successProb f ε ≥ 1 - δ := by
  sorry

end QAlgorithms.LearningSurvey
