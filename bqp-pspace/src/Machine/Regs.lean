/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Named wrapper registers and closed forms of the loop shapes used by the enumerator (S08).
-/
import Machine.Loop

set_option autoImplicit false

namespace ShiPPPSPACE

open Turing Turing.TM2 ShiSpace

/-- Contents of the seven wrapper registers. -/
structure Regs where
  inp : List Bool
  out : List Bool
  wit : List Bool
  cnt : List Bool
  tmp : List Bool
  nn : List Bool
  pq : List Bool

namespace Regs

def get (R : Regs) : Ext → List Bool
  | .inp => R.inp
  | .out => R.out
  | .wit => R.wit
  | .cnt => R.cnt
  | .tmp => R.tmp
  | .nn => R.nn
  | .pq => R.pq

def set (R : Regs) : Ext → List Bool → Regs
  | .inp, l => { R with inp := l }
  | .out, l => { R with out := l }
  | .wit, l => { R with wit := l }
  | .cnt, l => { R with cnt := l }
  | .tmp, l => { R with tmp := l }
  | .nn, l => { R with nn := l }
  | .pq, l => { R with pq := l }

@[simp] theorem get_set_self (R : Regs) (e : Ext) (l : List Bool) : (R.set e l).get e = l := by
  cases e <;> rfl

@[simp] theorem get_set_ne (R : Regs) (e e' : Ext) (l : List Bool) (h : e' ≠ e) :
    (R.set e l).get e' = R.get e' := by
  cases e <;> cases e' <;> first | rfl | exact absurd rfl h

theorem update_get (R : Regs) (e : Ext) (l : List Bool) :
    Function.update R.get e l = (R.set e l).get := by
  funext e'
  by_cases h : e' = e
  · subst h; simp
  · rw [Function.update_of_ne h, get_set_ne _ _ _ _ h]

@[simp] theorem get_inp (R : Regs) : R.get .inp = R.inp := rfl
@[simp] theorem get_out (R : Regs) : R.get .out = R.out := rfl
@[simp] theorem get_wit (R : Regs) : R.get .wit = R.wit := rfl
@[simp] theorem get_cnt (R : Regs) : R.get .cnt = R.cnt := rfl
@[simp] theorem get_tmp (R : Regs) : R.get .tmp = R.tmp := rfl
@[simp] theorem get_nn (R : Regs) : R.get .nn = R.nn := rfl
@[simp] theorem get_pq (R : Regs) : R.get .pq = R.pq := rfl

@[simp] theorem set_inp (R : Regs) (l : List Bool) : R.set .inp l = { R with inp := l } := rfl
@[simp] theorem set_out (R : Regs) (l : List Bool) : R.set .out l = { R with out := l } := rfl
@[simp] theorem set_wit (R : Regs) (l : List Bool) : R.set .wit l = { R with wit := l } := rfl
@[simp] theorem set_cnt (R : Regs) (l : List Bool) : R.set .cnt l = { R with cnt := l } := rfl
@[simp] theorem set_tmp (R : Regs) (l : List Bool) : R.set .tmp l = { R with tmp := l } := rfl
@[simp] theorem set_nn (R : Regs) (l : List Bool) : R.set .nn l = { R with nn := l } := rfl
@[simp] theorem set_pq (R : Regs) (l : List Bool) : R.set .pq l = { R with pq := l } := rfl

/-- Total register length. -/
def len (R : Regs) : ℕ :=
  R.inp.length + R.out.length + R.wit.length + R.cnt.length + R.tmp.length + R.nn.length +
    R.pq.length

theorem extSize_get (R : Regs) : extSize R.get = R.len := by
  unfold extSize len
  rw [show (Finset.univ : Finset Ext) = {.inp, .out, .wit, .cnt, .tmp, .nn, .pq} from rfl]
  simp [Finset.sum_insert]
  omega

/-- All registers empty. -/
def empty : Regs := ⟨[], [], [], [], [], [], []⟩

end Regs

@[simp] theorem update_join_get {κ : Type} [DecidableEq κ] {Γ : κ → Type}
    (chk : ∀ k, List (Γ k)) (R : Regs) (e : Ext) (l : List Bool) :
    Function.update (join chk R.get) (.inr e) l = join chk (R.set e l).get := by
  rw [update_join_inr, Regs.update_get]

/-! ### Closed forms of loop results -/

variable {κ : Type} [DecidableEq κ] {Γ : κ → Type}

theorem pushAll_append (a b : List (Tgt Γ)) (x : Bool) (S : Stacks Γ) :
    pushAll (a ++ b) x S = pushAll b x (pushAll a x S) := by
  induction a generalizing S with
  | nil => rfl
  | cons t a ih => exact ih _

theorem foldl_target (ts₁ ts₂ : List (Tgt Γ)) (i : κ ⊕ Ext) (f : Bool → HG Γ i)
    (h₁ : Avoids ts₁ i) (h₂ : Avoids ts₂ i) (w : List Bool) (S : Stacks Γ) :
    w.foldl (fun S b => pushAll (ts₁ ++ ⟨i, f⟩ :: ts₂) b S) S i = (w.map f).reverse ++ S i := by
  induction w generalizing S with
  | nil => rfl
  | cons b w ih =>
      rw [List.foldl_cons, ih, pushAll_append]
      simp only [pushAll]
      rw [pushAll_apply_ne h₂, Function.update_self, pushAll_apply_ne h₁]
      simp

theorem loopOut_clear (src : Ext) (w : List Bool) (S : Stacks Γ) :
    loopOut ([] : List (Tgt Γ)) src w S = Function.update S (.inr src) [] := by
  unfold loopOut
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

theorem loopOut_one (src : Ext) (i : κ ⊕ Ext) (f : Bool → HG Γ i) (hi : i ≠ .inr src)
    (w : List Bool) (S : Stacks Γ) :
    loopOut [⟨i, f⟩] src w S =
      Function.update (Function.update S (.inr src) []) i ((w.map f).reverse ++ S i) := by
  have hav : Avoids [⟨i, f⟩] (.inr src) := by
    intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact hi
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    unfold loopOut
    have := foldl_target [] [] j f (by simp [Avoids]) (by simp [Avoids]) w
      (Function.update S (.inr src) [])
    simpa [Function.update_of_ne hi] using this
  · rw [Function.update_of_ne hj]
    by_cases hs : j = .inr src
    · subst hs; rw [Function.update_self]; exact loopOut_src hav _ _
    · rw [Function.update_of_ne hs]
      exact loopOut_apply_ne j (by
        intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact Ne.symm hj) hs _ _

theorem loopOut_two (src : Ext) (i₁ i₂ : κ ⊕ Ext) (f₁ : Bool → HG Γ i₁) (f₂ : Bool → HG Γ i₂)
    (h₁ : i₁ ≠ .inr src) (h₂ : i₂ ≠ .inr src) (h₁₂ : i₁ ≠ i₂) (w : List Bool) (S : Stacks Γ) :
    loopOut [⟨i₁, f₁⟩, ⟨i₂, f₂⟩] src w S =
      Function.update (Function.update (Function.update S (.inr src) []) i₁
        ((w.map f₁).reverse ++ S i₁)) i₂ ((w.map f₂).reverse ++ S i₂) := by
  have hav : Avoids [⟨i₁, f₁⟩, ⟨i₂, f₂⟩] (.inr src) := by
    intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> assumption
  funext j
  by_cases hj₂ : j = i₂
  · subst hj₂
    rw [Function.update_self]
    unfold loopOut
    have := foldl_target [⟨i₁, f₁⟩] [] j f₂
      (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact h₁₂) (by simp [Avoids])
      w (Function.update S (.inr src) [])
    simpa [Function.update_of_ne h₂] using this
  · rw [Function.update_of_ne hj₂]
    by_cases hj₁ : j = i₁
    · subst hj₁
      rw [Function.update_self]
      unfold loopOut
      have := foldl_target [] [⟨i₂, f₂⟩] j f₁ (by simp [Avoids])
        (by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact Ne.symm h₁₂)
        w (Function.update S (.inr src) [])
      simpa [Function.update_of_ne h₁] using this
    · rw [Function.update_of_ne hj₁]
      by_cases hs : j = .inr src
      · subst hs; rw [Function.update_self]; exact loopOut_src hav _ _
      · rw [Function.update_of_ne hs]
        exact loopOut_apply_ne j (by
          intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact Ne.symm hj₁
          · exact Ne.symm hj₂) hs _ _

end ShiPPPSPACE
