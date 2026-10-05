import Definitions.Def_ShiClassPP
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiClassPP_gap_general_integer_linear_combination

namespace BQPReferenceValidation.Source23
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! LINCOMB: GENERAL INTEGER linear combinations of `ShiClassPP.gap` are realisable as the gap
of a SINGLE checker, at an EXPLICITLY BOUNDED witness length.  This is the ingredient that
CLOSE-COMB / CLOSE-COMBb name in their docstrings and do not prove: they cover coefficients of
the SHAPE `±2 ^ a` only.  Like them, this file is pure combinatorics about arbitrary checker
FUNCTIONS `R : Str × Str → Bool`; NO poly-time hypothesis appears anywhere.

INDEX CONVENTIONS -- identical to CLOSE-COMB, verified against the accepted files:

* Padding: the retained bits are the FIRST `m` of `m + k`, i.e. `b (Fin.castAdd k i)`; the `k`
  ignored bits are the trailing ones.
* One-bit split: the selector is the LAST bit, `b (Fin.last m)`, the tail is the first `m` bits
  `fun i : Fin m => b i.castSucc`, and `b (Fin.last m) = true` selects the SECOND checker.
* The n-ary split of conjunct (a) is the common generalisation of both: the first `m` bits
  `b (Fin.castAdd n i)` are the inner witness and the last `n` bits `b (Fin.natAdd m j)` are the
  case index, so `n = 0` is padding-by-zero and `n = 1` is the one-bit split.

ROUTE TAKEN.  Route (A) of the CLOSE-COMBb docstring -- binary expansion, iterated -- but in
HORNER form rather than as a sum over bit positions.  `d * G` is built by recursion on the bit
budget from `d = (d / 2) + ((d + 1) / 2)`: two recursive checkers at length `L + k` are joined
by ONE extra selector bit into a checker at length `L + k + 1`.  This needs only the ONE-BIT
split (conjunct (c) of CLOSE-COMB), never an n-ary selector, and it never needs to count how
many case indices fall in a given range -- which is exactly the expensive step that route (B)
("select a case index, pad the unused cases with a zero-gap checker") would have forced, since
that construction requires the cardinality of `{v : Fin n → Bool | val v < d}`.  The n-ary split
is proved anyway, as conjunct (a), because it is the natural statement of the identity and is
reusable; it is NOT used by the payoff.

THE PARITY OBSTRUCTION IS REAL, AND IT IS WHY `1 ≤ m₁`, `1 ≤ m₂` APPEAR IN (b).  `gap R x N`
is `2 * countAccept - 2 ^ N`, so it is EVEN whenever `1 ≤ N` and is `±1` when `N = 0`
(conjunct (e) proves both).  Hence `c₁ * gap R₁ x 0 + c₂ * gap R₂ x 0` can be odd -- take
`c₁ = 1`, `c₂ = 0` -- and then NO checker at any length `N ≥ 1` has that gap.  A brief that
asks for an unconditional `∃ R m` with an explicit `m ≥ 1` is therefore asking for a false
statement.  Two honest repairs are given instead: (b) assumes `1 ≤ m₁` and `1 ≤ m₂`, which is
free downstream since witness lengths there are `x.length ^ k ≥ 1` on nonempty inputs; and (c)
drops the assumption at the cost of realising `2 * (c₁ * gap R₁ x m₁ + c₂ * gap R₂ x m₂)`,
which has the SAME SIGN and therefore serves the threshold consumer identically.

THE LENGTH BOUND, which is the point of the exercise:
  `m = max m₁ m₂ + Nat.size (max c₁.natAbs c₂.natAbs) + 1`
`Nat.size k` is the number of binary digits of `k` (`k < 2 ^ Nat.size k`), so the overhead over
`max m₁ m₂` is `log₂ (max |c₁| |c₂|) + O(1)`: polynomial in the input whenever the coefficients
are `2 ^ poly`, as the `BQP ⊆ PP` consumer needs.  Conjunct (d) spells out the motivating case
`sign (D * q + 2 * B * a)` for GENERAL integers `q` and `a` and records that the constructed
checker's gap is positive exactly when that combination is.

Non-vacuity is asserted unconditionally in conjunct (f) at concrete checkers and literal
lengths, with coefficients `3` and `-5` -- neither a signed power of two, so the example is
outside CLOSE-COMBb's reach -- acting on gaps `2` and `-2` to give `16`; both sides are
evaluated independently by `decide`, and the realising length is the literal `6`. -/

open ShiClassPP PvsNP

/- ### Counting scaffolding (as in CLOSE-COMB) -/

private lemma card_pow (m : ℕ) : Fintype.card (Fin m → Bool) = 2 ^ m := by
  simp [Fintype.card_fun]

private lemma count_sum (R : Str × Str → Bool) (x : Str) (m : ℕ) :
    countAccept R x m = ∑ b : Fin m → Bool, if R (x, List.ofFn b) = true then 1 else 0 := by
  simp only [ShiClassPP.countAccept, Finset.card_filter]

private lemma sum_bool_two (f : Bool → ℕ) : ∑ c : Bool, f c = f false + f true := by
  have h : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

private lemma sum_pad (m k : ℕ) (G : (Fin m → Bool) → ℕ) :
    ∑ b : Fin (m + k) → Bool, G (fun i => b (Fin.castAdd k i))
      = 2 ^ k * ∑ u : Fin m → Bool, G u := by
  have h1 : ∑ p : (Fin m → Bool) × (Fin k → Bool), G p.1
      = ∑ b : Fin (m + k) → Bool, G (fun i => b (Fin.castAdd k i)) :=
    Fintype.sum_equiv (Fin.appendEquiv m k) _ _ (fun p => by simp)
  rw [← h1]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_const, Finset.card_univ, card_pow]
  try simp

private lemma sum_fin_one (F : (Fin 1 → Bool) → ℕ) :
    ∑ v : Fin 1 → Bool, F v = F (fun _ => false) + F (fun _ => true) := by
  rw [← Fintype.sum_equiv
      (⟨fun c _ => c, fun v => v 0, fun _ => rfl, fun v => funext fun i => by
        rw [Subsingleton.elim i 0]⟩ : Bool ≃ (Fin 1 → Bool))
      (fun c : Bool => F (fun _ => c)) F (fun _ => rfl)]
  exact sum_bool_two _

private lemma sum_split (m : ℕ) (G : (Fin (m + 1) → Bool) → ℕ) :
    ∑ b : Fin (m + 1) → Bool, G b
      = ∑ t : Fin m → Bool,
          (G (Fin.append t (fun _ => false)) + G (Fin.append t (fun _ => true))) := by
  have h1 : ∑ p : (Fin m → Bool) × (Fin 1 → Bool), G (Fin.append p.1 p.2)
      = ∑ b : Fin (m + 1) → Bool, G b :=
    Fintype.sum_equiv (Fin.appendEquiv m 1) _ _ (fun _ => by first | rfl | simp)
  rw [← h1]
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun _ _ => sum_fin_one _)

private lemma count_congr (R R' : Str × Str → Bool) (x : Str) (m : ℕ)
    (h : ∀ b : Fin m → Bool, R (x, List.ofFn b) = R' (x, List.ofFn b)) :
    countAccept R x m = countAccept R' x m := by
  rw [count_sum, count_sum]
  exact Finset.sum_congr rfl (fun b _ => by rw [h b])

private lemma pad_count (R R₁ : Str × Str → Bool) (x : Str) (m k : ℕ)
    (h : ∀ b : Fin (m + k) → Bool,
      R (x, List.ofFn b) = R₁ (x, List.ofFn (fun i : Fin m => b (Fin.castAdd k i)))) :
    countAccept R x (m + k) = 2 ^ k * countAccept R₁ x m := by
  rw [count_sum, count_sum,
    ← sum_pad m k (fun u => if R₁ (x, List.ofFn u) = true then 1 else 0)]
  exact Finset.sum_congr rfl (fun b _ => by rw [h b])

private lemma split_count (R R₁ R₂ : Str × Str → Bool) (x : Str) (m : ℕ)
    (h : ∀ b : Fin (m + 1) → Bool, R (x, List.ofFn b)
      = if b (Fin.last m) then R₂ (x, List.ofFn (fun i : Fin m => b i.castSucc))
        else R₁ (x, List.ofFn (fun i : Fin m => b i.castSucc))) :
    countAccept R x (m + 1) = countAccept R₁ x m + countAccept R₂ x m := by
  have hlast : (Fin.last m) = Fin.natAdd m (0 : Fin 1) := by
    refine Fin.ext ?_
    simp
  rw [count_sum, count_sum, count_sum, sum_split, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have e1 : ∀ (c : Bool) (i : Fin m), (Fin.append t (fun _ => c)) (Fin.castSucc i) = t i :=
    fun c i => Fin.append_left t (fun _ => c) i
  have e0 : ∀ c : Bool, (Fin.append t (fun _ => c)) (Fin.last m) = c := by
    intro c
    rw [hlast]
    exact Fin.append_right t (fun _ => c) 0
  rw [h, h]
  simp [e0, e1]

private lemma compl_count (R : Str × Str → Bool) (x : Str) (m : ℕ) :
    countAccept R x m + countAccept (fun p => !(R p)) x m = 2 ^ m := by
  rw [count_sum, count_sum, ← Finset.sum_add_distrib]
  have h1 : ∀ b : Fin m → Bool,
      ((if R (x, List.ofFn b) = true then 1 else 0)
        + (if (!(R (x, List.ofFn b))) = true then 1 else 0)) = 1 := by
    intro b
    cases hb : R (x, List.ofFn b) <;> simp
  rw [Finset.sum_congr rfl (fun b _ => h1 b)]
  simp [Finset.card_univ, card_pow]

private lemma pad_gap (R R₁ : Str × Str → Bool) (x : Str) (m k : ℕ)
    (h : ∀ b : Fin (m + k) → Bool,
      R (x, List.ofFn b) = R₁ (x, List.ofFn (fun i : Fin m => b (Fin.castAdd k i)))) :
    gap R x (m + k) = 2 ^ k * gap R₁ x m := by
  have hc := pad_count R R₁ x m k h
  simp only [ShiClassPP.gap, hc]
  push_cast
  ring

private lemma split_gap (R R₁ R₂ : Str × Str → Bool) (x : Str) (m : ℕ)
    (h : ∀ b : Fin (m + 1) → Bool, R (x, List.ofFn b)
      = if b (Fin.last m) then R₂ (x, List.ofFn (fun i : Fin m => b i.castSucc))
        else R₁ (x, List.ofFn (fun i : Fin m => b i.castSucc))) :
    gap R x (m + 1) = gap R₁ x m + gap R₂ x m := by
  have hc := split_count R R₁ R₂ x m h
  simp only [ShiClassPP.gap, hc]
  push_cast
  ring

private lemma compl_gap (R : Str × Str → Bool) (x : Str) (m : ℕ) :
    gap (fun p => !(R p)) x m = - gap R x m := by
  have h := compl_count R x m
  have hz : (countAccept R x m : ℤ) + (countAccept (fun p => !(R p)) x m : ℤ) = 2 ^ m := by
    exact_mod_cast h
  simp only [ShiClassPP.gap]
  linarith

private lemma gap_congr (R R' : Str × Str → Bool) (x : Str) (m : ℕ)
    (h : ∀ b : Fin m → Bool, R (x, List.ofFn b) = R' (x, List.ofFn b)) :
    gap R x m = gap R' x m := by
  simp only [ShiClassPP.gap, count_congr R R' x m h]

/- ### The n-ary split: the first `m` bits are the witness, the last `n` bits the case index -/

private lemma sum_nary (m n : ℕ) (H : (Fin n → Bool) → (Fin m → Bool) → ℕ) :
    ∑ b : Fin (m + n) → Bool,
        H (fun j : Fin n => b (Fin.natAdd m j)) (fun i : Fin m => b (Fin.castAdd n i))
      = ∑ v : Fin n → Bool, ∑ u : Fin m → Bool, H v u := by
  have h1 : ∑ p : (Fin m → Bool) × (Fin n → Bool), H p.2 p.1
      = ∑ b : Fin (m + n) → Bool,
          H (fun j : Fin n => b (Fin.natAdd m j)) (fun i : Fin m => b (Fin.castAdd n i)) :=
    Fintype.sum_equiv (Fin.appendEquiv m n) _ _
      (fun p => by simp [Fin.append_left, Fin.append_right])
  rw [← h1]
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_comm

private lemma nary_count (m n : ℕ) (R : Str × Str → Bool)
    (F : (Fin n → Bool) → Str × Str → Bool) (x : Str)
    (h : ∀ b : Fin (m + n) → Bool, R (x, List.ofFn b)
      = F (fun j : Fin n => b (Fin.natAdd m j))
          (x, List.ofFn (fun i : Fin m => b (Fin.castAdd n i)))) :
    countAccept R x (m + n) = ∑ v : Fin n → Bool, countAccept (F v) x m := by
  have key : ∑ b : Fin (m + n) → Bool,
        (if F (fun j : Fin n => b (Fin.natAdd m j))
            (x, List.ofFn (fun i : Fin m => b (Fin.castAdd n i))) = true then 1 else 0)
      = ∑ v : Fin n → Bool, ∑ u : Fin m → Bool,
          (if F v (x, List.ofFn u) = true then 1 else 0) :=
    sum_nary m n (fun v u => if F v (x, List.ofFn u) = true then 1 else 0)
  rw [count_sum]
  refine (Finset.sum_congr rfl (fun b _ => by rw [h b])).trans (key.trans ?_)
  exact Finset.sum_congr rfl (fun v _ => (count_sum (F v) x m).symm)

private lemma nary_gap (m n : ℕ) (R : Str × Str → Bool)
    (F : (Fin n → Bool) → Str × Str → Bool) (x : Str)
    (h : ∀ b : Fin (m + n) → Bool, R (x, List.ofFn b)
      = F (fun j : Fin n => b (Fin.natAdd m j))
          (x, List.ofFn (fun i : Fin m => b (Fin.castAdd n i)))) :
    gap R x (m + n) = ∑ v : Fin n → Bool, gap (F v) x m := by
  have hc := nary_count m n R F x h
  have hconst : (∑ _v : Fin n → Bool, (2 : ℤ) ^ m) = 2 ^ n * 2 ^ m := by
    rw [Finset.sum_const, Finset.card_univ, card_pow, nsmul_eq_mul]
    push_cast
    ring
  have hsplit : (∑ v : Fin n → Bool, gap (F v) x m)
      = (∑ v : Fin n → Bool, 2 * (countAccept (F v) x m : ℤ))
        - ∑ _v : Fin n → Bool, (2 : ℤ) ^ m := by
    rw [← Finset.sum_sub_distrib]
    rfl
  rw [hsplit, hconst, ← Finset.mul_sum]
  simp only [ShiClassPP.gap, hc]
  rw [Nat.cast_sum]
  ring

/- ### Reading a checker on a prefix of the witness, and the one-bit selector -/

private def pick (n : ℕ) (w : Str) : Str :=
  List.ofFn (fun i : Fin n => w.getD i.val false)

private lemma getD_ofFn {N : ℕ} (b : Fin N → Bool) (j : ℕ) (hj : j < N) :
    (List.ofFn b).getD j false = b ⟨j, hj⟩ := by
  have hlen : j < (List.ofFn b).length := by simpa using hj
  rw [List.getD_eq_getElem (List.ofFn b) false hlen]
  simp

private lemma pick_ofFn {n N : ℕ} (h : n ≤ N) (b : Fin N → Bool) :
    pick n (List.ofFn b) = List.ofFn (fun i : Fin n => b (Fin.castLE h i)) := by
  simp only [pick]
  exact congrArg List.ofFn (funext fun i => getD_ofFn b i.val (lt_of_lt_of_le i.2 h))

private lemma pick_self (M : ℕ) (b : Fin M → Bool) :
    pick M (List.ofFn b) = List.ofFn b := by
  simp only [pick]
  exact congrArg List.ofFn (funext fun i => getD_ofFn b i.val i.2)

private lemma pick_castSucc (M : ℕ) (b : Fin (M + 1) → Bool) :
    pick M (List.ofFn b) = List.ofFn (fun i : Fin M => b i.castSucc) := by
  simp only [pick]
  exact congrArg List.ofFn (funext fun i => getD_ofFn b i.val (by omega))

private lemma getD_last (M : ℕ) (b : Fin (M + 1) → Bool) :
    (List.ofFn b).getD M false = b (Fin.last M) :=
  getD_ofFn b M (by omega)

/-- `T` evaluated on the FIRST `M` bits of the witness. -/
private def pk (M : ℕ) (T : Str × Str → Bool) : Str × Str → Bool :=
  fun p => T (p.1, pick M p.2)

/-- Bit `M` of the witness selects `T₂` over `T₁`; both are read on the first `M` bits. -/
private def spl (M : ℕ) (T₁ T₂ : Str × Str → Bool) : Str × Str → Bool :=
  fun p => if p.2.getD M false then pk M T₂ p else pk M T₁ p

private lemma pk_gap (M : ℕ) (T : Str × Str → Bool) (x : Str) :
    gap (pk M T) x M = gap T x M :=
  gap_congr _ _ x M (fun b => by simp only [pk]; rw [pick_self M b])

private lemma pk_pad (M k : ℕ) (T : Str × Str → Bool) (x : Str) :
    gap (pk M T) x (M + k) = 2 ^ k * gap T x M := by
  refine pad_gap (pk M T) T x M k (fun b => ?_)
  simp only [pk]
  rw [pick_ofFn (Nat.le_add_right M k) b]
  first
    | rfl
    | exact rfl
    | simp only [Fin.castAdd]

private lemma spl_gap (M : ℕ) (T₁ T₂ : Str × Str → Bool) (x : Str) :
    gap (spl M T₁ T₂) x (M + 1) = gap T₁ x M + gap T₂ x M := by
  refine split_gap (spl M T₁ T₂) T₁ T₂ x M (fun b => ?_)
  simp only [spl, pk]
  rw [getD_last M b, pick_castSucc M b]

private lemma zc_gap (M : ℕ) (S : Str × Str → Bool) (x : Str) :
    gap (spl M S (fun p => !(S p))) x (M + 1) = 0 := by
  rw [spl_gap, compl_gap]
  ring

/- ### Horner recursion on the bit budget: every natural multiple is realisable -/

private lemma two_pow_le (a b : ℕ) (h : a ≤ b) : (2 : ℕ) ^ a ≤ 2 ^ b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  have h1 : 1 ≤ (2 : ℕ) ^ c := Nat.one_le_pow c 2 (by norm_num)
  have h2 : (2 : ℕ) ^ a * 1 ≤ 2 ^ a * 2 ^ c := Nat.mul_le_mul le_rfl h1
  rw [pow_add]
  simpa using h2

private lemma horner (x : Str) (S : Str × Str → Bool) (M : ℕ) :
    ∀ n : ℕ, ∀ d : ℕ, d ≤ 2 ^ n →
      ∃ T : Str × Str → Bool, gap T x (M + 1 + n) = (d : ℤ) * gap S x (M + 1) := by
  intro n
  induction n with
  | zero =>
      intro d hd
      have hd1 : d = 0 ∨ d = 1 := by
        rw [pow_zero] at hd
        omega
      rcases hd1 with rfl | rfl
      · refine ⟨spl M S (fun p => !(S p)), ?_⟩
        have hz : gap (spl M S (fun p => !(S p))) x (M + 1) = 0 := zc_gap M S x
        show gap (spl M S (fun p => !(S p))) x (M + 1) = ((0 : ℕ) : ℤ) * gap S x (M + 1)
        rw [hz]
        simp
      · refine ⟨S, ?_⟩
        show gap S x (M + 1) = ((1 : ℕ) : ℤ) * gap S x (M + 1)
        simp
  | succ k ih =>
      intro d hd
      have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hp] at hd
      obtain ⟨T₁, hT₁⟩ := ih (d / 2) (by omega)
      obtain ⟨T₂, hT₂⟩ := ih ((d + 1) / 2) (by omega)
      refine ⟨spl (M + 1 + k) T₁ T₂, ?_⟩
      have hg : gap (spl (M + 1 + k) T₁ T₂) x (M + 1 + k + 1)
          = gap T₁ x (M + 1 + k) + gap T₂ x (M + 1 + k) := spl_gap _ _ _ x
      show gap (spl (M + 1 + k) T₁ T₂) x (M + 1 + k + 1) = (d : ℤ) * gap S x (M + 1)
      rw [hg, hT₁, hT₂, ← add_mul]
      have hsum : ((d / 2 : ℕ) : ℤ) + (((d + 1) / 2 : ℕ) : ℤ) = (d : ℤ) := by
        have hn : d / 2 + (d + 1) / 2 = d := by omega
        exact_mod_cast hn
      rw [hsum]

private lemma scalar (x : Str) (S : Str × Str → Bool) (M n : ℕ) (c : ℤ)
    (hc : c.natAbs ≤ 2 ^ n) :
    ∃ T : Str × Str → Bool, gap T x (M + 1 + n) = c * gap S x (M + 1) := by
  obtain ⟨T, hT⟩ := horner x S M n c.natAbs hc
  by_cases h : 0 ≤ c
  · refine ⟨T, ?_⟩
    rw [hT]
    have hn : ((c.natAbs : ℤ)) = c := by omega
    rw [hn]
  · refine ⟨fun p => !(T p), ?_⟩
    rw [compl_gap, hT]
    have hn : ((c.natAbs : ℤ)) = -c := by omega
    rw [hn]
    ring

private lemma bicomb (x : Str) (R₁ R₂ : Str × Str → Bool) (M₁ M₂ n : ℕ) (c₁ c₂ : ℤ)
    (h₁ : c₁.natAbs ≤ 2 ^ n) (h₂ : c₂.natAbs ≤ 2 ^ n) :
    ∃ T : Str × Str → Bool,
      gap T x (max (M₁ + 1) (M₂ + 1) + n + 1)
        = c₁ * gap R₁ x (M₁ + 1) + c₂ * gap R₂ x (M₂ + 1) := by
  obtain ⟨k₁, hk₁, hn₁⟩ : ∃ k, M₁ + 1 + k = max (M₁ + 1) (M₂ + 1) + n ∧ n ≤ k :=
    ⟨max (M₁ + 1) (M₂ + 1) + n - (M₁ + 1), by omega, by omega⟩
  obtain ⟨k₂, hk₂, hn₂⟩ : ∃ k, M₂ + 1 + k = max (M₁ + 1) (M₂ + 1) + n ∧ n ≤ k :=
    ⟨max (M₁ + 1) (M₂ + 1) + n - (M₂ + 1), by omega, by omega⟩
  obtain ⟨T₁, hT₁⟩ := scalar x R₁ M₁ k₁ c₁ (le_trans h₁ (two_pow_le n k₁ hn₁))
  obtain ⟨T₂, hT₂⟩ := scalar x R₂ M₂ k₂ c₂ (le_trans h₂ (two_pow_le n k₂ hn₂))
  rw [hk₁] at hT₁
  rw [hk₂] at hT₂
  refine ⟨spl (max (M₁ + 1) (M₂ + 1) + n) T₁ T₂, ?_⟩
  rw [spl_gap, hT₁, hT₂]

/- ### The payoff -/

private lemma main_ge_one (x : Str) (R₁ R₂ : Str × Str → Bool) (m₁ m₂ : ℕ) (c₁ c₂ : ℤ)
    (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) :
    ∃ R : Str × Str → Bool,
      gap R x (max m₁ m₂ + Nat.size (max c₁.natAbs c₂.natAbs) + 1)
        = c₁ * gap R₁ x m₁ + c₂ * gap R₂ x m₂ := by
  obtain ⟨M₁, rfl⟩ : ∃ M, m₁ = M + 1 := ⟨m₁ - 1, by omega⟩
  obtain ⟨M₂, rfl⟩ : ∃ M, m₂ = M + 1 := ⟨m₂ - 1, by omega⟩
  have hs := Nat.lt_size_self (max c₁.natAbs c₂.natAbs)
  exact bicomb x R₁ R₂ M₁ M₂ (Nat.size (max c₁.natAbs c₂.natAbs)) c₁ c₂
    (by omega) (by omega)

private lemma main_any (x : Str) (R₁ R₂ : Str × Str → Bool) (m₁ m₂ : ℕ) (c₁ c₂ : ℤ) :
    ∃ R : Str × Str → Bool,
      gap R x (max m₁ m₂ + Nat.size (max c₁.natAbs c₂.natAbs) + 2)
        = 2 * (c₁ * gap R₁ x m₁ + c₂ * gap R₂ x m₂) := by
  obtain ⟨R, hR⟩ := main_ge_one x (pk m₁ R₁) (pk m₂ R₂) (m₁ + 1) (m₂ + 1) c₁ c₂
    (by omega) (by omega)
  have e1 : gap (pk m₁ R₁) x (m₁ + 1) = 2 * gap R₁ x m₁ := by
    rw [pk_pad m₁ 1 R₁ x]
    ring
  have e2 : gap (pk m₂ R₂) x (m₂ + 1) = 2 * gap R₂ x m₂ := by
    rw [pk_pad m₂ 1 R₂ x]
    ring
  have hmax : max (m₁ + 1) (m₂ + 1) = max m₁ m₂ + 1 := by omega
  rw [hmax, e1, e2] at hR
  refine ⟨R, ?_⟩
  rw [show max m₁ m₂ + Nat.size (max c₁.natAbs c₂.natAbs) + 2
      = max m₁ m₂ + 1 + Nat.size (max c₁.natAbs c₂.natAbs) + 1 from by omega, hR]
  ring

private lemma consumer (x : Str) (Rd Rb : Str × Str → Bool) (md mb : ℕ) (q a : ℤ)
    (hd : 1 ≤ md) (hb : 1 ≤ mb) :
    ∃ (R : Str × Str → Bool) (N : ℕ),
      N = max md mb + Nat.size (max q.natAbs (2 * a).natAbs) + 1
        ∧ gap R x N = gap Rd x md * q + 2 * gap Rb x mb * a
        ∧ (0 < gap R x N ↔ 0 < gap Rd x md * q + 2 * gap Rb x mb * a) := by
  obtain ⟨R, hR⟩ := main_ge_one x Rd Rb md mb q (2 * a) hd hb
  have hq : gap R x (max md mb + Nat.size (max q.natAbs (2 * a).natAbs) + 1)
      = gap Rd x md * q + 2 * gap Rb x mb * a := by
    rw [hR]
    ring
  exact ⟨R, _, rfl, hq, by rw [hq]⟩

private lemma parity (R : Str × Str → Bool) (x : Str) :
    (gap R x 0 = 1 ∨ gap R x 0 = -1)
      ∧ ∀ N : ℕ, 1 ≤ N → ∃ k : ℤ, gap R x N = 2 * k := by
  constructor
  · have hc : countAccept R x 0 = 0 ∨ countAccept R x 0 = 1 := by
      have h := compl_count R x 0
      rw [pow_zero] at h
      omega
    simp only [ShiClassPP.gap, pow_zero]
    rcases hc with h | h
    · right
      rw [h]
      norm_num
    · left
      rw [h]
      norm_num
  · intro N hN
    obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
    refine ⟨(countAccept R x (j + 1) : ℤ) - 2 ^ j, ?_⟩
    simp only [ShiClassPP.gap]
    ring

private lemma size5 : Nat.size 5 = 3 := by
  have h1 : Nat.size 5 ≤ 3 := Nat.size_le.2 (by norm_num)
  have h2 : 2 < Nat.size 5 := Nat.lt_size.2 (by norm_num)
  omega

private lemma concrete6 :
    ∃ R : Str × Str → Bool,
      gap R [] 6 = 3 * gap (fun p : Str × Str => decide (p.2.count true ≤ 1)) [] 2
        + (-5) * gap (fun p : Str × Str => decide (p.2.count true = 2)) [] 2 := by
  have h := main_ge_one ([] : Str)
    (fun p : Str × Str => decide (p.2.count true ≤ 1))
    (fun p : Str × Str => decide (p.2.count true = 2)) 2 2 3 (-5) (by omega) (by omega)
  have h5 : max (3 : ℤ).natAbs (-5 : ℤ).natAbs = 5 := by decide
  have h6 : Nat.size (max (3 : ℤ).natAbs (-5 : ℤ).natAbs) = 3 := by
    rw [h5]
    exact size5
  have he : max 2 2 + Nat.size (max (3 : ℤ).natAbs (-5 : ℤ).natAbs) + 1 = 6 := by omega
  rw [he] at h
  exact h

/- ### The public statement -/

theorem _root_.BQPReferenceValidation.candidate23 :
    -- (a) N-ARY SPLIT.  The first `m` witness bits are the inner witness, the last `n` are a
    -- case index; the count and the gap are the SUM over the `2 ^ n` cases.  `n = 0` is the
    -- padding identity and `n = 1` is CLOSE-COMB's one-bit split.
    (∀ (m n : ℕ) (R : Str × Str → Bool) (F : (Fin n → Bool) → Str × Str → Bool) (x : Str),
        (∀ b : Fin (m + n) → Bool, R (x, List.ofFn b)
          = F (fun j : Fin n => b (Fin.natAdd m j))
              (x, List.ofFn (fun i : Fin m => b (Fin.castAdd n i)))) →
        countAccept R x (m + n) = ∑ v : Fin n → Bool, countAccept (F v) x m
          ∧ gap R x (m + n) = ∑ v : Fin n → Bool, gap (F v) x m)
  ∧ -- (b) THE PAYOFF: GENERAL INTEGER coefficients, at an EXPLICIT length
    -- `max m₁ m₂ + Nat.size (max |c₁| |c₂|) + 1`, i.e. `max m₁ m₂ + log₂ (max |c₁| |c₂|) + O(1)`.
    -- The hypotheses `1 ≤ m₁`, `1 ≤ m₂` are NECESSARY: see (e).
    (∀ (R₁ R₂ : Str × Str → Bool) (x : Str) (m₁ m₂ : ℕ) (c₁ c₂ : ℤ),
        1 ≤ m₁ → 1 ≤ m₂ →
        ∃ R : Str × Str → Bool,
          gap R x (max m₁ m₂ + Nat.size (max c₁.natAbs c₂.natAbs) + 1)
            = c₁ * gap R₁ x m₁ + c₂ * gap R₂ x m₂)
  ∧ -- (c) THE UNCONDITIONAL VARIANT: no hypothesis on `m₁`, `m₂` at all, at the cost of an
    -- overall factor `2`, which does not change the SIGN of the combination.
    (∀ (R₁ R₂ : Str × Str → Bool) (x : Str) (m₁ m₂ : ℕ) (c₁ c₂ : ℤ),
        ∃ R : Str × Str → Bool,
          gap R x (max m₁ m₂ + Nat.size (max c₁.natAbs c₂.natAbs) + 2)
            = 2 * (c₁ * gap R₁ x m₁ + c₂ * gap R₂ x m₂))
  ∧ -- (d) THE MOTIVATING CONSUMER CASE, `sign (D * q + 2 * B * a)` for GENERAL integers `q`,
    -- `a`: one checker whose gap IS that combination, hence positive exactly when it is.
    (∀ (Rd Rb : Str × Str → Bool) (x : Str) (md mb : ℕ) (q a : ℤ),
        1 ≤ md → 1 ≤ mb →
        ∃ (R : Str × Str → Bool) (N : ℕ),
          N = max md mb + Nat.size (max q.natAbs (2 * a).natAbs) + 1
            ∧ gap R x N = gap Rd x md * q + 2 * gap Rb x mb * a
            ∧ (0 < gap R x N ↔ 0 < gap Rd x md * q + 2 * gap Rb x mb * a))
  ∧ -- (e) WHY `1 ≤ m` IS NEEDED, AND WHY (c) CARRIES A FACTOR `2`: a gap at length `0` is odd
    -- and a gap at any positive length is even, so an odd target is unrealisable above `0`.
    (∀ (R : Str × Str → Bool) (x : Str),
        (gap R x 0 = 1 ∨ gap R x 0 = -1)
          ∧ ∀ N : ℕ, 1 ≤ N → ∃ k : ℤ, gap R x N = 2 * k)
  ∧ -- (f) NON-VACUITY: concrete checkers, literal lengths, both sides evaluated independently,
    -- with coefficients `3` and `-5` -- NEITHER a signed power of two, so this instance is
    -- outside CLOSE-COMBb's payoff -- combining gaps `2` and `-2` into `16` at length `6`.
    ( gap (fun p : Str × Str => decide (p.2.count true ≤ 1)) [] 2 = 2
        ∧ gap (fun p : Str × Str => decide (p.2.count true = 2)) [] 2 = -2
        ∧ (3 : ℤ) * 2 + (-5 : ℤ) * (-2) = 16
        ∧ (3 : ℤ) * 2 + (-5 : ℤ) * (-2) ≠ (2 : ℤ) * 2 + (-2 : ℤ) * (-2)
        ∧ max (3 : ℤ).natAbs (-5 : ℤ).natAbs = 5
        ∧ Nat.size (max (3 : ℤ).natAbs (-5 : ℤ).natAbs) = 3
        ∧ max 2 2 + Nat.size (max (3 : ℤ).natAbs (-5 : ℤ).natAbs) + 1 = 6
        ∧ (∃ R : Str × Str → Bool,
            gap R [] 6 = 3 * gap (fun p : Str × Str => decide (p.2.count true ≤ 1)) [] 2
              + (-5) * gap (fun p : Str × Str => decide (p.2.count true = 2)) [] 2)
        -- the n-ary split of (a) at `m = 2`, `n = 1`, with the two cases genuinely different
        -- (`2` accepting witnesses versus `1`).
        ∧ (∀ b : Fin (2 + 1) → Bool,
            (fun p : Str × Str =>
                if p.2.getD 2 false then decide ((p.2.take 2).count true = 2)
                else decide ((p.2.take 2).count true = 1)) ([], List.ofFn b)
              = (fun (v : Fin 1 → Bool) (p : Str × Str) =>
                    if v 0 then decide (p.2.count true = 2)
                    else decide (p.2.count true = 1))
                  (fun j : Fin 1 => b (Fin.natAdd 2 j))
                  ([], List.ofFn (fun i : Fin 2 => b (Fin.castAdd 1 i))))
        ∧ countAccept (fun p : Str × Str =>
            if p.2.getD 2 false then decide ((p.2.take 2).count true = 2)
            else decide ((p.2.take 2).count true = 1)) [] 3 = 3
        ∧ (∑ v : Fin 1 → Bool,
            countAccept (fun p : Str × Str =>
              if v 0 then decide (p.2.count true = 2)
              else decide (p.2.count true = 1)) [] 2) = 3 ) := by
  refine ⟨fun m n R F x h => ⟨nary_count m n R F x h, nary_gap m n R F x h⟩,
    fun R₁ R₂ x m₁ m₂ c₁ c₂ h₁ h₂ => main_ge_one x R₁ R₂ m₁ m₂ c₁ c₂ h₁ h₂,
    fun R₁ R₂ x m₁ m₂ c₁ c₂ => main_any x R₁ R₂ m₁ m₂ c₁ c₂,
    fun Rd Rb x md mb q a hd hb => consumer x Rd Rb md mb q a hd hb,
    fun R x => parity R x, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, concrete6,
    by decide, by decide, by decide⟩
  · rw [show max (3 : ℤ).natAbs (-5 : ℤ).natAbs = 5 from by decide]
    exact size5
  · have h6 : Nat.size (max (3 : ℤ).natAbs (-5 : ℤ).natAbs) = 3 := by
      rw [show max (3 : ℤ).natAbs (-5 : ℤ).natAbs = 5 from by decide]
      exact size5
    omega

end BQPReferenceValidation.Source23

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate23
    let target ← getConstInfo ``ShiClassPP.gap_general_integer_linear_combination
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiClassPP.gap_general_integer_linear_combination"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiClassPP.gap_general_integer_linear_combination"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiClassPP.gap_general_integer_linear_combination"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate23
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiClassPP.gap_general_integer_linear_combination; axioms {axioms}"
