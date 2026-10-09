import QAlgorithms.Defs.Circuit

/-!
# Classical algorithms (shared definition layer)

Deterministic and randomized classical query algorithms, classical Boolean circuits, and the
expected number of i.i.d. samples until a stopping rule fires.
-/

namespace QAlgorithms

open scoped ENNReal

/-- de Wolf p.26 (§2.2), p.37 (§3.3.2); Childs p.30 (§5.3): a deterministic adaptive classical
query algorithm on inputs `x : ι → κ`, as a decision tree: at a `node` it queries position `i`
and branches on the answer `x i`; at a `leaf` it outputs `a`. -/
inductive DecisionTree (ι κ α : Type*) where
  /-- Stop and output `a`. -/
  | leaf (a : α)
  /-- Query position `i`, continue with `next (x i)`. -/
  | node (i : ι) (next : κ → DecisionTree ι κ α)

/-- The output of the decision tree on input `x`. -/
def DecisionTree.eval {ι κ α : Type*} : DecisionTree ι κ α → (ι → κ) → α
  | .leaf a, _ => a
  | .node i next, x => (next (x i)).eval x

/-- The number of queries made on input `x` (the length of the path `x` follows). -/
def DecisionTree.queries {ι κ α : Type*} : DecisionTree ι κ α → (ι → κ) → ℕ
  | .leaf _, _ => 0
  | .node i next, x => 1 + (next (x i)).queries x

/-- de Wolf p.37: the algorithm makes at most `T` queries on every input (on every path). -/
def DecisionTree.MakesAtMost {ι κ α : Type*} (t : DecisionTree ι κ α) (T : ℕ) : Prop :=
  ∀ x : ι → κ, t.queries x ≤ T

/-- de Wolf p.37 (§3.3.2: "the behavior of the randomized algorithm is an average over a number of
deterministic algorithms"), p.26, p.142 (Definition 3): a randomized classical query algorithm,
a probability distribution over deterministic decision trees. -/
abbrev RandDecisionTree (ι κ α : Type*) := PMF (DecisionTree ι κ α)

/-- Every deterministic algorithm in the support makes at most `T` queries on every input. -/
def RandMakesAtMost {ι κ α : Type*} (R : RandDecisionTree ι κ α) (T : ℕ) : Prop :=
  ∀ t ∈ R.support, t.MakesAtMost T

/-- The probability (over the algorithm's randomness) that the randomized algorithm `R` outputs
`a` on input `x`. -/
noncomputable def successProb {ι κ α : Type*} (R : RandDecisionTree ι κ α) (x : ι → κ) (a : α) :
    ℝ :=
  ((R.map fun t => t.eval x) a).toReal

/-- de Wolf p.25 (§2.1.1): the gate types of a classical Boolean circuit. -/
inductive BoolOp where
  | and
  | or
  | not

/-- A gate of a Boolean circuit, reading the wires with indices `a` and `b` (`b` is ignored by
`not`). -/
structure BoolGate where
  /-- The gate type. -/
  op : BoolOp
  /-- First input wire. -/
  a : ℕ
  /-- Second input wire (unused by `not`). -/
  b : ℕ

/-- de Wolf p.25 (§2.1.1): a Boolean circuit with `n` inputs and `m` outputs, as a straight-line
program over AND, OR, NOT gates: wires `0, …, n-1` carry the inputs and wire `n + k` carries the
output of gate `k`, which may only read earlier wires (`BoolCircuit.WellFormed`); `outputs j` is
the wire of output `j`. -/
structure BoolCircuit (n m : ℕ) where
  /-- The gates, in topological order. -/
  gates : List BoolGate
  /-- The designated output wires. -/
  outputs : Fin m → ℕ

/-- Every gate reads only wires defined before it, and every output is a defined wire. -/
def BoolCircuit.WellFormed {n m : ℕ} (C : BoolCircuit n m) : Prop :=
  (∀ k : Fin C.gates.length, (C.gates.get k).a < n + k ∧
    ((C.gates.get k).op = BoolOp.not ∨ (C.gates.get k).b < n + k)) ∧
  ∀ j : Fin m, C.outputs j < n + C.gates.length

/-- The value of one gate given the values of the wires defined so far. -/
def BoolGate.value (g : BoolGate) (vals : List Bool) : Bool :=
  match g.op with
  | .and => vals.getD g.a false && vals.getD g.b false
  | .or => vals.getD g.a false || vals.getD g.b false
  | .not => !vals.getD g.a false

/-- The values of all wires on input `x`. -/
def BoolCircuit.wireValues {n m : ℕ} (C : BoolCircuit n m) (x : Fin n → Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [g.value vals]) (List.ofFn x)

/-- The output of the circuit on input `x`. -/
def BoolCircuit.eval {n m : ℕ} (C : BoolCircuit n m) (x : Fin n → Bool) : Fin m → Bool :=
  fun j => (C.wireValues x).getD (C.outputs j) false

/-- de Wolf p.25: the size of a Boolean circuit, its number of AND/OR/NOT gates. -/
def BoolCircuit.size {n m : ℕ} (C : BoolCircuit n m) : ℕ :=
  C.gates.length

/-- The probability under `k` i.i.d. samples from `μ` that the sample sequence satisfies `E`. -/
noncomputable def iidProb {α : Type*} [Fintype α] (μ : PMF α) (k : ℕ) (E : (Fin k → α) → Prop) :
    ℝ≥0∞ :=
  open Classical in
  ∑ l : Fin k → α, if E l then ∏ i, μ (l i) else 0

/-- de Wolf p.36 (§3.2): the expected number `E[τ]` of i.i.d. samples from `μ` until the stopping
rule fires, where `τ` is the least `j` such that the first `j` samples satisfy `stop j`; computed
as `E[τ] = Σ_{k ≥ 0} Pr[τ > k]`, which is `⊤` when the rule fires with probability `< 1`.
Used for "the expected number of runs until `n − 1` independent equations". -/
noncomputable def expectedStoppingTime {α : Type*} [Fintype α] (μ : PMF α)
    (stop : (j : ℕ) → (Fin j → α) → Prop) : ℝ≥0∞ :=
  ∑' k : ℕ, iidProb μ k fun l => ∀ (j : ℕ) (h : j ≤ k), ¬ stop j (fun i => l (Fin.castLE h i))

/-! ### Sanity tests -/

example : (DecisionTree.node 0 (fun b : Bool => DecisionTree.leaf (α := Bool) (ι := Fin 2) b)).eval
    ![true, false] = true := rfl

example : (DecisionTree.node 1 (fun b : Bool => DecisionTree.leaf (α := Bool) (ι := Fin 2) b)).queries
    ![true, false] = 1 := rfl

/-- A one-gate circuit computing AND of two inputs. -/
example : (⟨[⟨BoolOp.and, 0, 1⟩], fun _ => 2⟩ : BoolCircuit 2 1).eval ![true, true] 0 = true ∧
    (⟨[⟨BoolOp.and, 0, 1⟩], fun _ => 2⟩ : BoolCircuit 2 1).eval ![true, false] 0 = false := by
  decide

/-- A rule that fires immediately (on the empty prefix) has expected stopping time `0`. -/
example {α : Type*} [Fintype α] (μ : PMF α) : expectedStoppingTime μ (fun _ _ => True) = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun k => ?_
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [if_neg]
  intro h
  exact h 0 (Nat.zero_le k) trivial

end QAlgorithms
