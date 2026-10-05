/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Enumeration order and prefix accepting counts (plan task S06).
-/
import Count.FixedBits
import Definitions.Def_ShiClassPP

set_option autoImplicit false

/-!
# Prefix counts agree with `ShiClassPP.countAccept`

`prefixCount R x m j` counts accepting witnesses among the first `j` words of width `m` in
increment order. It is a mathematical specification only; the machine stores just one word and
a binary counter. At `j = 2^m` it equals `countAccept R x m`, the count over
`Fin m → Bool` used by `PP` (via `List.ofFn`), including the unique empty word when `m = 0`.
-/

namespace ShiPPPSPACE

open PvsNP

/-- Accepting witnesses among words `word m 0, …, word m (j-1)`. -/
def prefixCount (R : Str × Str → Bool) (x : Str) (m j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun i => R (x, word m i) = true)).card

@[simp] theorem prefixCount_zero (R : Str × Str → Bool) (x : Str) (m : ℕ) :
    prefixCount R x m 0 = 0 := by
  simp [prefixCount]

theorem prefixCount_succ (R : Str × Str → Bool) (x : Str) (m j : ℕ) :
    prefixCount R x m (j + 1) =
      prefixCount R x m j + if R (x, word m j) = true then 1 else 0 := by
  unfold prefixCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem prefixCount_le (R : Str × Str → Bool) (x : Str) (m j : ℕ) :
    prefixCount R x m j ≤ j := by
  unfold prefixCount
  exact le_trans (Finset.card_filter_le _ _) (by simp)

theorem exists_ofFn_eq (l : List Bool) (m : ℕ) (h : l.length = m) :
    ∃ b : Fin m → Bool, List.ofFn b = l := by
  subst h
  exact ⟨fun i => l[i], List.ofFn_getElem⟩

/-- **Agreement with the PP counting scaffold.** -/
theorem prefixCount_full (R : Str × Str → Bool) (x : Str) (m : ℕ) :
    prefixCount R x m (2 ^ m) = ShiClassPP.countAccept R x m := by
  classical
  unfold prefixCount ShiClassPP.countAccept
  let φ : (Fin m → Bool) → ℕ := fun b => val (List.ofFn b)
  have hφ : Function.Injective φ := by
    intro b b' h
    apply List.ofFn_injective
    exact val_injective_of_length _ _ (by simp) h
  rw [← Finset.card_image_of_injective _ hφ]
  congr 1
  ext i
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨hi, hR⟩
    obtain ⟨b, hb⟩ := exists_ofFn_eq (word m i) m (length_word m i)
    refine ⟨b, by rw [hb]; exact hR, ?_⟩
    simp only [φ, hb]
    exact val_word_of_lt m i hi
  · rintro ⟨b, hb, rfl⟩
    refine ⟨by simpa [φ] using val_lt (List.ofFn b), ?_⟩
    rw [show φ b = val (List.ofFn b) from rfl, word_val_of_length _ _ (by simp)]
    exact hb

/-- Strict-majority acceptance in terms of the final prefix count. -/
theorem pp_condition_iff (R : Str × Str → Bool) (x : Str) (k : ℕ) :
    2 * ShiClassPP.countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k) ↔
      2 * prefixCount R x (x.length ^ k) (2 ^ (x.length ^ k)) > 2 ^ (x.length ^ k) := by
  rw [prefixCount_full]

/-- The accepting count fits in `m+1` bits, even when every witness accepts. -/
theorem prefixCount_lt (R : Str × Str → Bool) (x : Str) (m j : ℕ) (hj : j ≤ 2 ^ m) :
    prefixCount R x m j < 2 ^ (m + 1) := by
  have := prefixCount_le R x m j
  have : 0 < 2 ^ m := by positivity
  rw [pow_succ]
  omega

/-- Boundary cases fixed by the plan. -/
example : (0 : ℕ) ^ 0 = 1 := rfl
example (R : Str × Str → Bool) : ShiClassPP.countAccept R [] 0 =
    if R ([], []) = true then 1 else 0 := by
  rw [← prefixCount_full, pow_zero, show (1 : ℕ) = 0 + 1 from rfl, prefixCount_succ]
  simp only [prefixCount_zero, zero_add, word]
  by_cases h : R ([], []) = true <;> simp [h]

end ShiPPPSPACE
