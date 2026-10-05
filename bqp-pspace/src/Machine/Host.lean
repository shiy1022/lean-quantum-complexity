/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Host stack/state types for the enumerator and their stack algebra (plan tasks S07–S10).
-/
import Space.PeakComposition

set_option autoImplicit false

/-!
# Host types

The enumerator's stacks are `κ ⊕ Ext`: the embedded checker's stacks `κ` (alphabets `Γ`) and a
fixed finite set of Boolean wrapper registers `Ext`. Its internal state is `σ × Reg`: the
checker's state and a two-bit wrapper register (last popped bit, whether a symbol was present).
`join chk ext` assembles a host stack assignment from checker stacks and wrapper registers.
-/

namespace ShiPPPSPACE

open Turing Turing.TM2

/-- Wrapper registers, all over `Bool`. -/
inductive Ext
  | inp  -- master input
  | out  -- final answer
  | wit  -- current witness word (little-endian)
  | cnt  -- accepting counter (little-endian, width m+1)
  | tmp  -- reversal scratch
  | nn   -- unary copy of the input length
  | pq   -- unary product scratch
  deriving DecidableEq, Repr

instance : Fintype Ext where
  elems := {.inp, .out, .wit, .cnt, .tmp, .nn, .pq}
  complete := by intro x; cases x <;> decide

/-- Host stack alphabets. -/
abbrev HG {κ : Type} (Γ : κ → Type) (i : κ ⊕ Ext) : Type :=
  Sum.casesOn (motive := fun _ => Type) i Γ (fun _ => Bool)

/-- Wrapper register: last popped bit, and whether the pop found a symbol. -/
abbrev Reg := Bool × Bool

section Join

variable {κ : Type} {Γ : κ → Type}

/-- Assemble host stacks from checker stacks and wrapper registers. -/
def join (chk : ∀ k, List (Γ k)) (ext : Ext → List Bool) : ∀ i, List (HG Γ i)
  | .inl k => chk k
  | .inr e => ext e

@[simp] theorem join_inl (chk : ∀ k, List (Γ k)) (ext : Ext → List Bool) (k : κ) :
    join chk ext (.inl k) = chk k := rfl

@[simp] theorem join_inr (chk : ∀ k, List (Γ k)) (ext : Ext → List Bool) (e : Ext) :
    join chk ext (.inr e) = ext e := rfl

theorem join_eta (S : ∀ i, List (HG Γ i)) :
    join (fun k => S (.inl k)) (fun e => S (.inr e)) = S := by
  funext i; rcases i with k | e <;> rfl

variable [DecidableEq κ]

@[simp] theorem update_join_inr (chk : ∀ k, List (Γ k)) (ext : Ext → List Bool) (e : Ext)
    (l : List Bool) :
    Function.update (join chk ext) (.inr e) l = join chk (Function.update ext e l) := by
  funext i
  rcases i with k | e'
  · simp [Function.update, join]
  · by_cases h : e' = e
    · subst h; simp [Function.update, join]
    · simp [Function.update, join, h]

@[simp] theorem update_join_inl (chk : ∀ k, List (Γ k)) (ext : Ext → List Bool) (k : κ)
    (l : List (Γ k)) :
    Function.update (join chk ext) (.inl k) l = join (Function.update chk k l) ext := by
  funext i
  rcases i with k' | e
  · by_cases h : k' = k
    · subst h; simp [Function.update, join]
    · simp [Function.update, join, h]
  · simp [Function.update, join]

end Join

/-! ### Space of host stacks -/

section Size

variable {K : Type} [DecidableEq K] [Fintype K] {G : K → Type}

/-- Exact space change of replacing one stack. -/
theorem size_update (S : ∀ k, List (G k)) (j : K) (l : List (G j)) :
    ShiTMStackGrowth.size (Function.update S j l) + (S j).length =
      ShiTMStackGrowth.size S + l.length := by
  classical
  unfold ShiTMStackGrowth.size
  have h1 : ∀ k, (Function.update S j l k).length =
      Function.update (fun k => (S k).length) j l.length k := fun k =>
    Function.apply_update (fun k (x : List (G k)) => x.length) S j l k
  simp only [h1]
  rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem size_update_cons (S : ∀ k, List (G k)) (j : K) (a : G j) :
    ShiTMStackGrowth.size (Function.update S j (a :: S j)) = ShiTMStackGrowth.size S + 1 := by
  have := size_update S j (a :: S j)
  simp at this
  omega

theorem size_update_tail (S : ∀ k, List (G k)) (j : K) (a : G j) (l : List (G j))
    (h : S j = a :: l) :
    ShiTMStackGrowth.size (Function.update S j l) + 1 = ShiTMStackGrowth.size S := by
  have := size_update S j l
  rw [h] at this
  simp at this
  omega

end Size

theorem size_join {κ : Type} [DecidableEq κ] [Fintype κ] {Γ : κ → Type}
    (chk : ∀ k, List (Γ k)) (ext : Ext → List Bool) :
    ShiTMStackGrowth.size (join chk ext) =
      ShiTMStackGrowth.size chk + ∑ e, (ext e).length := by
  unfold ShiTMStackGrowth.size
  rw [Fintype.sum_sum_type]
  rfl

/-- Total length of the wrapper registers. -/
def extSize (ext : Ext → List Bool) : ℕ := ∑ e, (ext e).length

theorem extSize_update (ext : Ext → List Bool) (e : Ext) (l : List Bool) :
    extSize (Function.update ext e l) + (ext e).length = extSize ext + l.length := by
  have := size_update (G := fun _ : Ext => Bool) ext e l
  simpa [ShiTMStackGrowth.size, extSize] using this

end ShiPPPSPACE
