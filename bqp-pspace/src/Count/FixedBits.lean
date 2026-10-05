/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Fixed-width little-endian binary words and increment (plan task S05).
-/
import Mathlib

set_option autoImplicit false

/-!
# Fixed-width binary words

Words are `List Bool`, **least significant bit first** (the list head; on a stack, the top).
`val` reads a word; `word m n` writes `n mod 2^m` in width `m`; `inc` is ripple-carry
increment returning the new word of the same width and an overflow flag. At width zero the
only word is `[]`, and incrementing it overflows.
-/

namespace ShiPPPSPACE

/-- Little-endian value. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * val w

@[simp] theorem val_nil : val [] = 0 := rfl
@[simp] theorem val_cons (b : Bool) (w : List Bool) : val (b :: w) = b.toNat + 2 * val w := rfl

theorem val_lt (w : List Bool) : val w < 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
      simp only [val_cons, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

/-- Width-`m` little-endian encoding of `n mod 2^m`. -/
def word : ℕ → ℕ → List Bool
  | 0, _ => []
  | m + 1, n => (n % 2 == 1) :: word m (n / 2)

@[simp] theorem length_word (m n : ℕ) : (word m n).length = m := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih => simp [word, ih]

theorem val_word (m n : ℕ) : val (word m n) = n % 2 ^ m := by
  induction m generalizing n with
  | zero => simp [word, Nat.mod_one]
  | succ m ih =>
      simp only [word, val_cons, ih]
      rw [pow_succ', Nat.mod_mul]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem word_val (w : List Bool) : word w.length (val w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      simp only [List.length_cons, word, val_cons]
      congr 1
      · cases b <;> simp
      · rw [show (b.toNat + 2 * val w) / 2 = val w by cases b <;> simp; omega, ih]

theorem word_val_of_length (w : List Bool) (m : ℕ) (h : w.length = m) : word m (val w) = w := by
  subst h; exact word_val w

theorem val_word_of_lt (m n : ℕ) (h : n < 2 ^ m) : val (word m n) = n := by
  rw [val_word, Nat.mod_eq_of_lt h]

theorem word_injOn (m a b : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ m) (h : word m a = word m b) :
    a = b := by
  rw [← val_word_of_lt m a ha, ← val_word_of_lt m b hb, h]

theorem val_injective_of_length (u w : List Bool) (hl : u.length = w.length) (h : val u = val w) :
    u = w := by
  rw [← word_val u, ← word_val w, hl, h]

/-- Ripple-carry increment: the new word and an overflow flag. -/
def inc : List Bool → List Bool × Bool
  | [] => ([], true)
  | false :: w => (true :: w, false)
  | true :: w => (false :: (inc w).1, (inc w).2)

@[simp] theorem length_inc (w : List Bool) : (inc w).1.length = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [inc, ih]

/-- The increment law, with the overflow weight `2^width`. -/
theorem val_inc (w : List Bool) :
    val (inc w).1 + (if (inc w).2 then 2 ^ w.length else 0) = val w + 1 := by
  induction w with
  | nil => simp [inc]
  | cons b w ih =>
      cases b with
      | false => simp [inc]; omega
      | true =>
          simp only [inc, val_cons, List.length_cons, pow_succ]
          split_ifs at ih ⊢ with h <;> simp at ih ⊢ <;> omega

theorem val_inc_of_not_overflow (w : List Bool) (h : (inc w).2 = false) :
    val (inc w).1 = val w + 1 := by
  simpa [h] using val_inc w

theorem inc_overflow_iff (w : List Bool) : (inc w).2 = true ↔ val w + 1 = 2 ^ w.length := by
  constructor
  · intro h
    have hi := val_inc w
    have hl := val_lt w
    simp [h] at hi
    omega
  · intro h
    by_contra h'
    simp only [Bool.not_eq_true] at h'
    have := val_inc_of_not_overflow w h'
    have := val_lt (inc w).1
    rw [length_inc] at this
    omega

theorem val_inc_of_overflow (w : List Bool) (h : (inc w).2 = true) : val (inc w).1 = 0 := by
  have := val_inc w
  have h2 := (inc_overflow_iff w).1 h
  simp [h] at this
  omega

/-- Enumeration order: incrementing the width-`m` word of `j` gives the word of `j+1`, and
overflows exactly at the last word `2^m - 1`, returning to the zero word. -/
theorem inc_word (m j : ℕ) (hj : j < 2 ^ m) :
    inc (word m j) = (word m (j + 1), decide (j + 1 = 2 ^ m)) := by
  have hv := val_word_of_lt m j hj
  by_cases hlast : j + 1 = 2 ^ m
  · have ho : (inc (word m j)).2 = true := by
      rw [inc_overflow_iff, hv, length_word]; exact hlast
    have h0 := val_inc_of_overflow _ ho
    have hw : (inc (word m j)).1 = word m (j + 1) := by
      apply val_injective_of_length
      · simp
      · rw [h0, val_word, hlast, Nat.mod_self]
    simp [Prod.ext_iff, hw, ho, hlast]
  · have ho : (inc (word m j)).2 = false := by
      by_contra h
      simp only [Bool.not_eq_false] at h
      rw [inc_overflow_iff, hv, length_word] at h
      exact hlast h
    have h1 := val_inc_of_not_overflow _ ho
    have hw : (inc (word m j)).1 = word m (j + 1) := by
      apply val_injective_of_length
      · simp
      · rw [h1, hv, val_word_of_lt m (j + 1) (by omega)]
    simp [Prod.ext_iff, hw, ho, hlast]

theorem word_zero (m : ℕ) : word m 0 = List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [word, ih, List.replicate_succ]

/-! ### Small executable checks (widths 0, 1, 2); the general facts are proved above. -/

example : inc [] = ([], true) := rfl
example : inc [false] = ([true], false) := rfl
example : inc [true] = ([false], true) := rfl
example : (List.range 4).map (word 2) = [[false, false], [true, false], [false, true], [true, true]] := by
  decide
example : inc [true, true] = ([false, false], true) := rfl
example : val [false, true] = 2 := rfl

end ShiPPPSPACE
