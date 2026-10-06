/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.ExecutionLemmas

/-!
# Q16 — an existing BQP verifier in the new semantics

For an existing layered circuit `c : ShiShallow.Layered (n + m)`, input `x : Bits n` and output
wire `out`, `bqpDesc c x out` is the zero-message verifier whose single block

1. prepares the classical input explicitly with `X` gates on the wires `i` with `x i = true`
   (`prepList`; the plan requires classical inputs to be prepared by gates), then
2. runs the gates of `c` in order (layers flattened, `Instr.toGate`).

* `bqpDesc_valid`: the description is valid;
* **`accept_bqpDesc`**: every prover is accepted with probability exactly
  `ShiShallow.acceptProb c x out`, the existing BQP acceptance.

Supporting facts: `Gate.toInstr?` inverts `Instr.toGate`; `runLayered c = runLayer c.flatten`;
`X` gates flip bits (`runLayer_xGates`); the prepared state is `ShiShallow.inputState x`
(`runLayer_prepList_zeroVec`).
-/

namespace ShiQIP

open Matrix ShiQuantum ShiShallow

/-! ## From instructions to syntax and back -/

/-- An established instruction as description syntax. -/
def _root_.ShiShallow.Instr.toGate {N : ℕ} : Instr N → Gate
  | .h i => .h i
  | .s i => .s i
  | .t i => .t i
  | .x i => .x i
  | .cnot i j _ => .cnot i j

theorem toInstr?_toGate {N : ℕ} (g : Instr N) : Gate.toInstr? N g.toGate = some g := by
  cases g with
  | h i => simp [Instr.toGate, Gate.toInstr?, i.isLt]
  | s i => simp [Instr.toGate, Gate.toInstr?, i.isLt]
  | t i => simp [Instr.toGate, Gate.toInstr?, i.isLt]
  | x i => simp [Instr.toGate, Gate.toInstr?, i.isLt]
  | cnot i j hij =>
    have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    simp [Instr.toGate, Gate.toInstr?, i.isLt, j.isLt, this]

theorem filterMap_toInstr?_map_toGate {N : ℕ} (l : List (Instr N)) :
    (l.map Instr.toGate).filterMap (Gate.toInstr? N) = l := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [toInstr?_toGate, ih]

/-! ## Runs of instruction lists -/

theorem runLayer_append {N : ℕ} (l₁ l₂ : List (Instr N)) (ψ : QState N) :
    runLayer (l₁ ++ l₂) ψ = runLayer l₂ (runLayer l₁ ψ) := by
  simp [runLayer, List.foldl_append]

theorem runLayered_eq_runLayer_flatten {N : ℕ} (c : Layered N) (ψ : QState N) :
    runLayered c ψ = runLayer c.flatten ψ := by
  induction c generalizing ψ with
  | nil => rfl
  | cons l c ih =>
    rw [List.flatten_cons, runLayer_append, ← ih]
    rfl

/-- An `X` gate flips its wire. -/
theorem apply_x {N : ℕ} (i : Fin N) (ψ : QState N) (y : Bits N) :
    (Instr.x i).apply ψ y = ψ (Function.update y i (!y i)) := by
  simp only [Instr.apply, apply1, Fintype.sum_bool, xMat, of_apply]
  cases y i <;> simp

/-- Flip the wires of a list, last first. -/
def flips {N : ℕ} : List (Fin N) → Bits N → Bits N
  | [], y => y
  | i :: L, y => Function.update (flips L y) i (!(flips L y) i)

theorem runLayer_xGates {N : ℕ} (L : List (Fin N)) (ψ : QState N) (y : Bits N) :
    runLayer (L.map Instr.x) ψ y = ψ (flips L y) := by
  induction L generalizing ψ with
  | nil => rfl
  | cons i L ih =>
    change runLayer (L.map Instr.x) ((Instr.x i).apply ψ) y = _
    rw [ih, apply_x]
    rfl

theorem flips_apply {N : ℕ} {L : List (Fin N)} (hL : L.Nodup) (y : Bits N) (w : Fin N) :
    flips L y w = if w ∈ L then !y w else y w := by
  induction L with
  | nil => simp [flips]
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    simp only [flips]
    by_cases hw : w = i
    · subst hw
      rw [Function.update_self, ih hL.2, if_neg hL.1, if_pos List.mem_cons_self]
    · rw [Function.update_of_ne hw, ih hL.2]
      simp [hw]

/-! ## Preparing the classical input -/

/-- The `X` gates loading `x` into the first `n` wires. -/
def prepWires {n m : ℕ} (x : Bits n) : List (Fin (n + m)) :=
  ((List.finRange n).filter fun i => x i).map (Fin.castAdd m)

def prepList {n m : ℕ} (x : Bits n) : List (Instr (n + m)) := (prepWires (m := m) x).map Instr.x

theorem prepWires_nodup {n m : ℕ} (x : Bits n) : (prepWires (m := m) x).Nodup :=
  ((List.nodup_finRange n).filter _).map (Fin.castAdd_injective n m)

theorem mem_prepWires {n m : ℕ} (x : Bits n) (w : Fin (n + m)) :
    w ∈ prepWires (m := m) x ↔ ∃ i : Fin n, x i = true ∧ Fin.castAdd m i = w := by
  simp [prepWires]

/-- The prepared state is the existing `inputState x`. -/
theorem runLayer_prepList_zeroVec {n m : ℕ} (x : Bits n) :
    runLayer (prepList (m := m) x) (zeroVec (n + m)) = inputState x := by
  funext y
  rw [prepList, runLayer_xGates, zeroVec, inputState]
  have key : flips (prepWires (m := m) x) y = Qubits.zero (n + m) ↔
      (∀ i : Fin n, y (Fin.castAdd m i) = x i) ∧ ∀ k : Fin m, y (Fin.natAdd n k) = false := by
    rw [funext_iff]
    simp only [flips_apply (prepWires_nodup x), Qubits.zero]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun k => ?_⟩
      · have := h (Fin.castAdd m i)
        by_cases hx : x i = true
        · rw [if_pos ((mem_prepWires x _).mpr ⟨i, hx, rfl⟩)] at this
          simpa [hx] using this
        · have hn : Fin.castAdd m i ∉ prepWires (m := m) x := by
            rw [mem_prepWires]
            rintro ⟨i', hi', he⟩
            exact hx (Fin.castAdd_injective n m he ▸ hi')
          rw [if_neg hn] at this
          simpa [hx] using this
      · have := h (Fin.natAdd n k)
        have hn : Fin.natAdd n k ∉ prepWires (m := m) x := by
          rw [mem_prepWires]
          rintro ⟨i', _, he⟩
          have := congrArg Fin.val he
          simp at this
          omega
        rwa [if_neg hn] at this
    · rintro ⟨h1, h2⟩ w
      refine Fin.addCases (fun i => ?_) (fun k => ?_) w
      · by_cases hx : x i = true
        · rw [if_pos ((mem_prepWires x _).mpr ⟨i, hx, rfl⟩), h1 i, hx]; rfl
        · have hn : Fin.castAdd m i ∉ prepWires (m := m) x := by
            rw [mem_prepWires]
            rintro ⟨i', hi', he⟩
            exact hx (Fin.castAdd_injective n m he ▸ hi')
          rw [if_neg hn, h1 i]
          simpa using hx
      · have hn : Fin.natAdd n k ∉ prepWires (m := m) x := by
          rw [mem_prepWires]
          rintro ⟨i', _, he⟩
          have := congrArg Fin.val he
          simp at this
          omega
        rw [if_neg hn, h2 k]
  by_cases h : flips (prepWires (m := m) x) y = Qubits.zero (n + m)
  · rw [if_pos h, if_pos (key.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mpr h'))]

/-! ## The BQP verifier as a zero-message description -/

/-- The zero-message verifier for circuit `c`, input `x` and output wire `out`. -/
def bqpDesc {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) : Desc :=
  ⟨n + m, out, [], [(prepList (m := m) x ++ c.flatten).map Instr.toGate]⟩

theorem bqpDesc_totalWires {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    (bqpDesc c x out).totalWires = n + m := rfl

theorem okBool_toGate_private {N : ℕ} (d : Desc) (hpriv : d.priv = N) (g : Instr N) :
    (Instr.toGate g).okBool (d.held 0) = true := by
  have hw : ∀ i : Fin N, d.held 0 i = true := fun i => by
    simp [Desc.held, hpriv, i.isLt]
  cases g with
  | h i => exact hw i
  | s i => exact hw i
  | t i => exact hw i
  | x i => exact hw i
  | cnot i j hij =>
    have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    simp [Instr.toGate, Gate.okBool, hw, this]

theorem bqpDesc_valid {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    (bqpDesc c x out).Valid := by
  simp only [Desc.Valid, Desc.check, bqpDesc, Bool.and_eq_true]
  refine ⟨⟨⟨decide_eq_true out.isLt, rfl⟩, rfl⟩, ?_⟩
  simp only [Desc.blocksOkFrom, List.all_eq_true, Bool.and_true, List.mem_map]
  rintro _ ⟨g, -, rfl⟩
  exact okBool_toGate_private (N := n + m) _ rfl g

/-- **The existing BQP acceptance is reproduced exactly, for every prover.** -/
theorem accept_bqpDesc {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m))
    (P : Prover (bqpDesc c x out)) : accept P = acceptProb c x out := by
  rw [accept_of_numMsgs_eq_zero rfl]
  have ho : ∀ y : Qubits (bqpDesc c x out).totalWires,
      outBit (bqpDesc c x out) y ↔ y out = true := fun y =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨out.isLt, h⟩⟩
  simp only [ho]
  change (∑ y : Bits (n + m), if y out = true then
    ‖runLayer (((prepList (m := m) x ++ c.flatten).map Instr.toGate).filterMap
      (Gate.toInstr? (n + m))) (zeroVec (n + m)) y‖ ^ 2 else 0) = _
  rw [filterMap_toInstr?_map_toGate, runLayer_append, runLayer_prepList_zeroVec,
    ← runLayered_eq_runLayer_flatten]
  rfl

end ShiQIP
