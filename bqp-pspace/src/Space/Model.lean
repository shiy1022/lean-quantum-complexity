/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The corrected finite-multistack polynomial-space class (plan task S01).

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Language
import «AMPUNI-run-stack-growth»

set_option autoImplicit false

/-!
# Polynomial space for bundled multi-stack machines

The space of a configuration is the total length of all its stacks, input and output
included (`ShiTMStackGrowth.size`). A machine is space-bounded on an input when **every**
configuration reachable from the initial one by iterating Mathlib's step function satisfies
the bound; this includes the initial and the halted configuration.

`PSPACE` asks for a *total* machine (`Turing.TM2Computable`, which supplies a halting run with
the correct output on every input) together with a polynomial (natural coefficients) bounding
the space of that same machine on every input. **No time bound is imposed.** This deliberately
differs from the historical `Def_ShiClassPSPACE` bundle, which required
`TM2ComputableInPolyTime` and a bare `n ^ k` space bound; no equivalence with that class, or
with a single-tape read-only-input model, is claimed.
-/

namespace ShiSpace

open Turing

/-- Finiteness data carried by every bundled machine, exposed as instances. These are the
structure's own fields, so all uses agree definitionally. -/
instance finTM2_kFin (tm : FinTM2) : Fintype tm.K := tm.kFin
instance finTM2_ΛFin (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin
instance finTM2_σFin (tm : FinTM2) : Fintype tm.σ := tm.σFin

/-- The space used by a configuration: the total length of all its stacks. -/
def cfgSpace (tm : FinTM2) (c : tm.Cfg) : ℕ :=
  ShiTMStackGrowth.size c.stk

/-- Every configuration reachable from the initial configuration on `xs`, including the
initial and halted ones, uses at most `s` stack cells. -/
def SpaceBoundedOn (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (s : ℕ) : Prop :=
  ∀ (t : ℕ) (c : tm.Cfg),
    (ShiTMSubroutine.run tm.m)^[t] (some (initList tm xs)) = some c → cfgSpace tm c ≤ s

/-- `χ` is decided by a total bundled machine whose space is bounded by a polynomial in the
input length, on every input. The correctness certificate and the space bound concern the
same machine `c.tm`. -/
def PolySpaceDecider (χ : List Bool → Bool) : Prop :=
  ∃ c : TM2Computable (id : List Bool → List Bool) Computability.encodeBool χ,
    ∃ p : Polynomial ℕ, ∀ x : List Bool,
      SpaceBoundedOn c.tm (x.map c.inputAlphabet.invFun) (p.eval x.length)

/-- **`PSPACE`** (corrected finite-multistack model): languages decided by a total machine
using polynomial space on every reachable configuration. -/
def PSPACE : Set (Language Bool) :=
  {L | ∃ χ : List Bool → Bool, PolySpaceDecider χ ∧ ∀ x, x ∈ L ↔ χ x = true}

/-! ### Elementary lemmas -/

/-- `run` is definitionally the iteration used by Mathlib's `EvalsTo`. -/
theorem run_eq_flip_bind (tm : FinTM2) :
    ShiTMSubroutine.run tm.m = flip Option.bind tm.step := rfl

theorem initList_stk_self (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    (initList tm xs).stk tm.k₀ = xs := by
  simp [initList]

theorem initList_stk_ne (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (k : tm.K) (hk : k ≠ tm.k₀) :
    (initList tm xs).stk k = [] := by
  simp [initList, hk]

theorem haltList_stk_self (tm : FinTM2) (ys : List (tm.Γ tm.k₁)) :
    (haltList tm ys).stk tm.k₁ = ys := by
  simp [haltList]

theorem haltList_stk_ne (tm : FinTM2) (ys : List (tm.Γ tm.k₁)) (k : tm.K) (hk : k ≠ tm.k₁) :
    (haltList tm ys).stk k = [] := by
  simp [haltList, hk]

/-- The initial configuration uses exactly the input length. -/
theorem cfgSpace_initList (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    cfgSpace tm (initList tm xs) = xs.length := by
  unfold cfgSpace ShiTMStackGrowth.size
  rw [Finset.sum_eq_single tm.k₀]
  · rw [initList_stk_self]
  · intro k _ hk
    rw [initList_stk_ne tm xs k hk, List.length_nil]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The halted configuration uses exactly the output length. -/
theorem cfgSpace_haltList (tm : FinTM2) (ys : List (tm.Γ tm.k₁)) :
    cfgSpace tm (haltList tm ys) = ys.length := by
  unfold cfgSpace ShiTMStackGrowth.size
  rw [Finset.sum_eq_single tm.k₁]
  · rw [haltList_stk_self]
  · intro k _ hk
    rw [haltList_stk_ne tm ys k hk, List.length_nil]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A Boolean answer occupies exactly one cell in the final configuration. -/
theorem cfgSpace_haltList_encodeBool (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (b : Bool) :
    cfgSpace tm (haltList tm ((Computability.encodeBool b).map e.invFun)) = 1 := by
  rw [cfgSpace_haltList]
  rfl

theorem SpaceBoundedOn.mono {tm : FinTM2} {xs : List (tm.Γ tm.k₀)} {s s' : ℕ}
    (h : SpaceBoundedOn tm xs s) (hs : s ≤ s') : SpaceBoundedOn tm xs s' :=
  fun t c hc => le_trans (h t c hc) hs

/-- The bound must accommodate the input itself. -/
theorem SpaceBoundedOn.input_le {tm : FinTM2} {xs : List (tm.Γ tm.k₀)} {s : ℕ}
    (h : SpaceBoundedOn tm xs s) : xs.length ≤ s := by
  have h0 := h 0 (initList tm xs) rfl
  rwa [cfgSpace_initList] at h0

/-- The bound covers the halted configuration of any successful run. -/
theorem SpaceBoundedOn.output_le {tm : FinTM2} {xs : List (tm.Γ tm.k₀)} {s : ℕ}
    {ys : List (tm.Γ tm.k₁)} (h : SpaceBoundedOn tm xs s) (ho : TM2Outputs tm xs (some ys)) :
    ys.length ≤ s := by
  have hc := h ho.steps (haltList tm ys) ho.evals_in_steps
  rwa [cfgSpace_haltList] at hc

/-- A space-bounded configuration sequence stays bounded after the machine halts: the
iterate is then `none`, which carries no configuration. -/
theorem SpaceBoundedOn.of_iterate_le {tm : FinTM2} {xs : List (tm.Γ tm.k₀)} {s : ℕ}
    (h : ∀ (t : ℕ) (c : tm.Cfg),
      (ShiTMSubroutine.run tm.m)^[t] (some (initList tm xs)) = some c → cfgSpace tm c ≤ s) :
    SpaceBoundedOn tm xs s := h

theorem PolySpaceDecider.mono {χ : List Bool → Bool}
    (c : TM2Computable (id : List Bool → List Bool) Computability.encodeBool χ)
    (p q : Polynomial ℕ) (hpq : ∀ n, p.eval n ≤ q.eval n)
    (hp : ∀ x : List Bool,
      SpaceBoundedOn c.tm (x.map c.inputAlphabet.invFun) (p.eval x.length)) :
    PolySpaceDecider χ :=
  ⟨c, q, fun x => (hp x).mono (hpq _)⟩

/-- Any polynomial space bound forces the space polynomial to dominate the input length:
initialization alone costs `x.length`. -/
theorem PolySpaceDecider.length_le {χ : List Bool → Bool}
    (c : TM2Computable (id : List Bool → List Bool) Computability.encodeBool χ)
    (p : Polynomial ℕ)
    (hp : ∀ x : List Bool,
      SpaceBoundedOn c.tm (x.map c.inputAlphabet.invFun) (p.eval x.length))
    (x : List Bool) : x.length ≤ p.eval x.length := by
  simpa using (hp x).input_le

theorem mem_PSPACE {L : Language Bool} :
    L ∈ PSPACE ↔ ∃ χ : List Bool → Bool, PolySpaceDecider χ ∧ ∀ x, x ∈ L ↔ χ x = true :=
  Iff.rfl

end ShiSpace
