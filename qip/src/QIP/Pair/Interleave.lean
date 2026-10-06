/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Syntax

/-!
# Segment layouts

A list of widths `a = [a₀, a₁, …]` describes consecutive segments; segment `i` starts at the
prefix sum `psum a i`. `zw a b` is the interleaved layout `a₀+b₀, a₁+b₁, …`.

* `exists_segment`, `segment_unique`, `segIdx`, `segIdx_spec`, `segIdx_eq`: every position lies
  in exactly one segment, computed by `segIdx`;
* `psum_zw`, `getD_zw`, `sum_zw`: prefix sums, widths and totals of the interleaved layout.
-/

namespace ShiQIP

/-- Prefix sums: the start of segment `i`. -/
def psum (a : List ℕ) (i : ℕ) : ℕ := (a.take i).sum

/-- Segment widths of the interleaved layout. -/
def zw (a b : List ℕ) : List ℕ := List.zipWith (· + ·) a b

@[simp] theorem psum_zero (a : List ℕ) : psum a 0 = 0 := by simp [psum]

@[simp] theorem psum_cons_succ (x : ℕ) (a : List ℕ) (i : ℕ) :
    psum (x :: a) (i + 1) = x + psum a i := by simp [psum]

theorem psum_add_getD_le : ∀ (a : List ℕ) (i : ℕ), psum a i + a.getD i 0 ≤ a.sum
  | [], i => by simp [psum]
  | x :: a, 0 => by simp [psum]
  | x :: a, i + 1 => by
    have := psum_add_getD_le a i
    simp only [psum_cons_succ, List.getD_cons_succ, List.sum_cons]
    omega

/-- Every position lies in a segment. -/
theorem exists_segment : ∀ (a : List ℕ) (v : ℕ), v < a.sum →
    ∃ i, psum a i ≤ v ∧ v < psum a i + a.getD i 0
  | [], v, h => by simp at h
  | x :: a, v, h => by
    by_cases hv : v < x
    · exact ⟨0, by simp, by simpa using hv⟩
    · simp only [List.sum_cons] at h
      obtain ⟨i, h1, h2⟩ := exists_segment a (v - x) (by omega)
      refine ⟨i + 1, ?_, ?_⟩
      · simp only [psum_cons_succ]; omega
      · simp only [psum_cons_succ, List.getD_cons_succ]; omega

/-- A position lies in only one segment. -/
theorem segment_unique : ∀ (a : List ℕ) {v i j : ℕ}, psum a i ≤ v → v < psum a i + a.getD i 0 →
    psum a j ≤ v → v < psum a j + a.getD j 0 → i = j
  | [], v, i, j, _, h2, _, _ => by simp [psum] at h2
  | x :: a, v, 0, 0, _, _, _, _ => rfl
  | x :: a, v, 0, j + 1, _, h2, h3, _ => by
    simp only [psum_zero, List.getD_cons_zero, zero_add, psum_cons_succ] at h2 h3; omega
  | x :: a, v, i + 1, 0, h1, _, _, h4 => by
    simp only [psum_zero, List.getD_cons_zero, zero_add, psum_cons_succ] at h1 h4; omega
  | x :: a, v, i + 1, j + 1, h1, h2, h3, h4 => by
    simp only [psum_cons_succ, List.getD_cons_succ] at h1 h2 h3 h4
    have := segment_unique a (v := v - x) (i := i) (j := j) (by omega) (by omega) (by omega)
      (by omega)
    omega

theorem psum_zw : ∀ (a b : List ℕ), a.length = b.length → ∀ i,
    psum (zw a b) i = psum a i + psum b i
  | [], [], _, i => by simp [psum, zw]
  | x :: a, y :: b, h, 0 => by simp
  | x :: a, y :: b, h, i + 1 => by
    have := psum_zw a b (by simpa using h) i
    simp only [zw, List.zipWith_cons_cons] at this ⊢
    simp only [psum_cons_succ, this]
    ring
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem getD_zw : ∀ (a b : List ℕ), a.length = b.length → ∀ i,
    (zw a b).getD i 0 = a.getD i 0 + b.getD i 0
  | [], [], _, i => by simp [zw]
  | x :: a, y :: b, h, 0 => by simp [zw]
  | x :: a, y :: b, h, i + 1 => by
    have := getD_zw a b (by simpa using h) i
    simp only [zw, List.zipWith_cons_cons, List.getD_cons_succ] at this ⊢
    exact this
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem sum_zw : ∀ (a b : List ℕ), a.length = b.length → (zw a b).sum = a.sum + b.sum
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    have := sum_zw a b (by simpa using h)
    simp only [zw, List.zipWith_cons_cons, List.sum_cons] at this ⊢
    rw [this]; ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## Segment index -/

/-- The segment containing a position. -/
def segIdx : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: a, v => if v < x then 0 else segIdx a (v - x) + 1

theorem segIdx_spec : ∀ (a : List ℕ) (v : ℕ), v < a.sum →
    psum a (segIdx a v) ≤ v ∧ v < psum a (segIdx a v) + a.getD (segIdx a v) 0
  | [], v, h => by simp at h
  | x :: a, v, h => by
    by_cases hv : v < x
    · simp [segIdx, hv]
    · simp only [List.sum_cons] at h
      have := segIdx_spec a (v - x) (by omega)
      simp only [segIdx, if_neg hv, psum_cons_succ, List.getD_cons_succ]
      omega

theorem segIdx_eq {a : List ℕ} {v i : ℕ} (h1 : psum a i ≤ v) (h2 : v < psum a i + a.getD i 0) :
    segIdx a v = i := by
  have hv : v < a.sum := lt_of_lt_of_le h2 (psum_add_getD_le a i)
  obtain ⟨s1, s2⟩ := segIdx_spec a v hv
  exact segment_unique a s1 s2 h1 h2

end ShiQIP
