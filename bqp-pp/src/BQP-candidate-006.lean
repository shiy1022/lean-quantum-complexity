import Definitions.Def_ShiClassRel
import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Theorems.Thm_ShiBQP_acceptance_in_the_ring_adjoining_root_two_decides_pp_membership

namespace BQPReferenceValidation.Source6

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiClassPP PvsNP

/-! ASM-CONS: THE FINAL CONSUMER, arithmetic half.

Given the acceptance probability in the ring `ℤ[√2]` -- the shape `BRIDGE-SEMb` reaches once
`ASM-ACC` (conjunct (6)) and `ASM-CARD` (`C d = N d`) identify its pair counts with the SINGLE
counts `N d = countAccept (R d) (enc Q) (hc Q)` of `CHECK-1f` over the DOUBLED program -- this
slice carries the verdict all the way to `L ∈ ShiClassPP.PP`.

The chain, all of it proved here:
* the `1/2` threshold on `p = (1/2)^h (A + B√2)` is the SIGN of `D + 2B√2`, `D = 2A - 2^h`,
  and the `BQP` promise keeps that quantity `2^h/3` away from `0`;
* `s = h + 3` bits of dyadic precision are enough: with `q = 2^s` and any integer `a` with
  `a² ≤ 2q² < (a+1)²` the IRRATIONAL sign test equals the INTEGER sign test `0 < Dq + 2Ba`;
* `a = Nat.sqrt (2 * 4^s)` is such an `a`;
* the counts are gaps: `gap (R d) z (2h) = 2 N d - 4^h`, hence `A` is available ONLY doubled
  (`gap R₀ - gap R₄ = 2A`) and `B` only doubled (`gap R₁ - gap R₃ = 2B`) -- but `D` itself is
  `(gap R₀ - gap R₄) - 2^h`, so only `B` forces the doubled test `0 < 2Dq + 2(2B)a`;
* a poly-time checker whose gap IS that combination puts `L` in `PP`.

The two inputs that are NOT proved here are the two that `ASM-ACC`/`ASM-CARD` supply, plus the
existence of the explicit combined poly-time checker; all three enter as hypotheses. -/

private lemma four_pow_real (h : ℕ) : (4 : ℝ) ^ h = (2 : ℝ) ^ h * (2 : ℝ) ^ h := by
  rw [← mul_pow]; norm_num

private lemma four_pow_nat (s : ℕ) : (4 : ℕ) ^ s = (2 ^ s) ^ 2 := by
  induction s with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ih]; ring

private lemma two_pow_two_mul (h : ℕ) : (2 : ℕ) ^ (2 * h) = 4 ^ h := by
  rw [pow_mul]; norm_num

private lemma two_pow_two_mul_int (h : ℕ) : (2 : ℤ) ^ (2 * h) = 4 ^ h := by
  rw [pow_mul]; norm_num

private lemma natAbs_sub_le (m n P : ℕ) (hm : m ≤ P) (hn : n ≤ P) :
    ((m : ℤ) - (n : ℤ)).natAbs ≤ P := by omega

/-- Shifting the `1/2` threshold: `D + 2B√2 = 2·2^h·p - 2^h`, with `D = 2A - 2^h`. -/
private lemma shift_id (h : ℕ) (A B : ℤ) (p : ℝ)
    (hp : p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2)) :
    ((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2
      = 2 * (2 : ℝ) ^ h * p - (2 : ℝ) ^ h := by
  have hpow : (2 : ℝ) ^ h * (1 / 2 : ℝ) ^ h = 1 := by
    rw [← mul_pow]; norm_num
  have hX : (2 : ℝ) ^ h * ((1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2))
      = (A : ℝ) + (B : ℝ) * Real.sqrt 2 := by
    rw [← mul_assoc, hpow, one_mul]
  rw [hp]
  push_cast
  linarith [hX]

private lemma prom_hi (h : ℕ) (A B : ℤ) (p : ℝ)
    (hp : p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2))
    (h23 : (2 : ℝ) / 3 ≤ p) :
    (2 : ℝ) ^ h / 3 ≤ ((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 := by
  have hu : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  rw [shift_id h A B p hp]
  nlinarith [hu, h23]

private lemma prom_lo (h : ℕ) (A B : ℤ) (p : ℝ)
    (hp : p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2))
    (h13 : p ≤ (1 : ℝ) / 3) :
    ((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ≤ -((2 : ℝ) ^ h / 3) := by
  have hu : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  rw [shift_id h A B p hp]
  nlinarith [hu, h13]

/-- THE PRECISION LEMMA. `s = h + 3` dyadic bits suffice. -/
private lemma approx_sign (h : ℕ) (D B q a : ℤ)
    (hq : q = 2 ^ (h + 3)) (ha0 : 0 ≤ a)
    (hs1 : a ^ 2 ≤ 2 * q ^ 2) (hs2 : 2 * q ^ 2 < (a + 1) ^ 2)
    (hB : B.natAbs ≤ 4 ^ h)
    (hprom : (2 : ℝ) ^ h / 3 ≤ (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2
        ∨ (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ≤ -((2 : ℝ) ^ h / 3)) :
    ((0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ↔ 0 < D * q + 2 * B * a) := by
  have hu : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have hr0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hrsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hqR : (q : ℝ) = 8 * (2 : ℝ) ^ h := by rw [hq]; push_cast; ring
  have hqpos : (0 : ℝ) < (q : ℝ) := by rw [hqR]; linarith
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
  have hs1R : (a : ℝ) ^ 2 ≤ 2 * (q : ℝ) ^ 2 := by exact_mod_cast hs1
  have hs2R : 2 * (q : ℝ) ^ 2 < ((a : ℝ) + 1) ^ 2 := by exact_mod_cast hs2
  have hqr : ((q : ℝ) * Real.sqrt 2) ^ 2 = 2 * (q : ℝ) ^ 2 := by
    rw [mul_pow, hrsq]; ring
  have hqrpos : (0 : ℝ) < (q : ℝ) * Real.sqrt 2 := mul_pos hqpos hr0
  have hle : (a : ℝ) ≤ (q : ℝ) * Real.sqrt 2 := by
    nlinarith [hs1R, hqr, hqrpos, haR]
  have hlt : (q : ℝ) * Real.sqrt 2 < (a : ℝ) + 1 := by
    nlinarith [hs2R, hqr, hqrpos, haR]
  have hB1 : (B.natAbs : ℤ) ≤ (4 : ℤ) ^ h := by exact_mod_cast hB
  rw [Int.natCast_natAbs] at hB1
  have hBb := abs_le.mp hB1
  have hBhi : (B : ℝ) ≤ (2 : ℝ) ^ h * (2 : ℝ) ^ h := by
    have hb : (B : ℝ) ≤ (4 : ℝ) ^ h := by exact_mod_cast hBb.2
    rw [four_pow_real] at hb; exact hb
  have hBlo : -((2 : ℝ) ^ h * (2 : ℝ) ^ h) ≤ (B : ℝ) := by
    have hb : -((4 : ℝ) ^ h) ≤ (B : ℝ) := by exact_mod_cast hBb.1
    rw [four_pow_real] at hb; exact hb
  have heps0 : (0 : ℝ) ≤ (q : ℝ) * Real.sqrt 2 - (a : ℝ) := by linarith
  have heps1 : (q : ℝ) * Real.sqrt 2 - (a : ℝ) ≤ 1 := by linarith
  have hcast : ((D * q + 2 * B * a : ℤ) : ℝ)
      = (q : ℝ) * ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
        - 2 * (B : ℝ) * ((q : ℝ) * Real.sqrt 2 - (a : ℝ)) := by
    push_cast; ring
  set eps := (q : ℝ) * Real.sqrt 2 - (a : ℝ) with hepsdef
  have hEhi : 2 * (B : ℝ) * eps ≤ 2 * ((2 : ℝ) ^ h * (2 : ℝ) ^ h) := by
    nlinarith [heps0, heps1, hBhi, hBlo, mul_pos hu hu]
  have hElo : -(2 * ((2 : ℝ) ^ h * (2 : ℝ) ^ h)) ≤ 2 * (B : ℝ) * eps := by
    nlinarith [heps0, heps1, hBhi, hBlo, mul_pos hu hu]
  constructor
  · intro hX
    have hXlo : (2 : ℝ) ^ h / 3 ≤ (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 := by
      rcases hprom with h1 | h2
      · exact h1
      · exfalso; linarith
    have hqX : (q : ℝ) * ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
        = 8 * (2 : ℝ) ^ h * ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2) := by rw [hqR]
    have hpos : (0 : ℝ) < ((D * q + 2 * B * a : ℤ) : ℝ) := by
      rw [hcast, hqX]
      nlinarith [hu, hXlo, hEhi, mul_pos hu hu]
    exact_mod_cast hpos
  · intro hY
    by_contra hX
    push_neg at hX
    have hXhi : (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ≤ -((2 : ℝ) ^ h / 3) := by
      rcases hprom with h1 | h2
      · exfalso; linarith
      · exact h2
    have hqX : (q : ℝ) * ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
        = 8 * (2 : ℝ) ^ h * ((D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2) := by rw [hqR]
    have hneg : ((D * q + 2 * B * a : ℤ) : ℝ) < 0 := by
      rw [hcast, hqX]
      nlinarith [hu, hXhi, hElo, mul_pos hu hu]
    have hposR : (0 : ℝ) < ((D * q + 2 * B * a : ℤ) : ℝ) := by exact_mod_cast hY
    linarith

private lemma sqrt_bounds (s : ℕ) :
    (0 : ℤ) ≤ (Nat.sqrt (2 * 4 ^ s) : ℤ)
      ∧ (Nat.sqrt (2 * 4 ^ s) : ℤ) ^ 2 ≤ 2 * ((2 : ℤ) ^ s) ^ 2
      ∧ 2 * ((2 : ℤ) ^ s) ^ 2 < ((Nat.sqrt (2 * 4 ^ s) : ℤ) + 1) ^ 2 := by
  have heq : 2 * 4 ^ s = 2 * (2 ^ s : ℕ) ^ 2 := by rw [four_pow_nat s]
  have hA : Nat.sqrt (2 * 4 ^ s) ^ 2 ≤ 2 * (2 ^ s : ℕ) ^ 2 :=
    le_trans (Nat.sqrt_le' (2 * 4 ^ s)) (le_of_eq heq)
  have hB : 2 * (2 ^ s : ℕ) ^ 2 < (Nat.sqrt (2 * 4 ^ s) + 1) ^ 2 := by
    have hh := Nat.lt_succ_sqrt' (2 * 4 ^ s)
    have hh2 : 2 * (2 ^ s : ℕ) ^ 2 < Nat.succ (Nat.sqrt (2 * 4 ^ s)) ^ 2 :=
      lt_of_le_of_lt (le_of_eq heq.symm) hh
    simpa [Nat.succ_eq_add_one] using hh2
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast hA, by exact_mod_cast hB⟩

private lemma gap_pos_iff (R : Str × Str → Bool) (x : Str) (m : ℕ) :
    0 < gap R x m ↔ 2 ^ m < 2 * countAccept R x m := by
  have h1 : ((2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m := by push_cast; ring
  have h2 : gap R x m = 2 * (countAccept R x m : ℤ) - ((2 ^ m : ℕ) : ℤ) := by
    rw [h1]; rfl
  rw [h2, sub_pos]
  constructor <;> intro hh <;> exact_mod_cast hh

private lemma mem_PP_of_gap (L : Language Bool) (Rf : Str × Str → Bool) (k : ℕ)
    (hpt : PolyTimeChecker Rf)
    (hiff : ∀ x : Str, x ∈ L ↔ 0 < gap Rf x (x.length ^ k)) :
    L ∈ ShiClassPP.PP :=
  ⟨Rf, k, hpt, fun x => by rw [gt_iff_lt, hiff x, gap_pos_iff]⟩

private lemma mem_PPof_of_gap (L : Language Bool) (Rf : Str × Str → Bool) (k : ℕ)
    (hpt : PolyTimeChecker Rf)
    (hiff : ∀ x : Str, x ∈ L ↔ 0 < gap Rf x (x.length ^ k)) :
    L ∈ ShiClassRel.PPof PvsNP.PolyTimeChecker :=
  ⟨Rf, k, hpt, fun x => by rw [gt_iff_lt, hiff x, gap_pos_iff]⟩

theorem _root_.BQPReferenceValidation.candidate6 :
    -- (1) THE THRESHOLD SHIFT.  `p = (1/2)^h (A + B√2)` compares with `1/2` exactly as
    -- `D = 2A - 2^h` compares with `-2B√2`, and the `BQP` promise leaves a `2^h/3` margin.
    (∀ (h : ℕ) (A B : ℤ) (p : ℝ),
        p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2) →
        (((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2
            = 2 * (2 : ℝ) ^ h * p - (2 : ℝ) ^ h)
          ∧ ((2 : ℝ) / 3 ≤ p →
              (2 : ℝ) ^ h / 3 ≤ ((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2)
          ∧ (p ≤ (1 : ℝ) / 3 →
              ((2 * A - 2 ^ h : ℤ) : ℝ) + 2 * (B : ℝ) * Real.sqrt 2
                ≤ -((2 : ℝ) ^ h / 3)))
  ∧ -- (2) THE PRECISION LEMMA.  At `s = h + 3` dyadic bits the irrational sign test IS the
    -- integer sign test.  `q = 2^s`; `a` is ANY integer with `a² ≤ 2q² < (a+1)²`.
    (∀ (h : ℕ) (D B q a : ℤ),
        q = 2 ^ (h + 3) → 0 ≤ a → a ^ 2 ≤ 2 * q ^ 2 → 2 * q ^ 2 < (a + 1) ^ 2 →
        B.natAbs ≤ 4 ^ h →
        ((2 : ℝ) ^ h / 3 ≤ (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2
            ∨ (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ≤ -((2 : ℝ) ^ h / 3)) →
        ((0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ↔ 0 < D * q + 2 * B * a))
  ∧ -- (2') `a = Nat.sqrt (2 * 4^s)` is such an integer, so the test is fully explicit.
    (∀ s : ℕ,
        (0 : ℤ) ≤ (Nat.sqrt (2 * 4 ^ s) : ℤ)
          ∧ (Nat.sqrt (2 * 4 ^ s) : ℤ) ^ 2 ≤ 2 * ((2 : ℤ) ^ s) ^ 2
          ∧ 2 * ((2 : ℤ) ^ s) ^ 2 < ((Nat.sqrt (2 * 4 ^ s) : ℤ) + 1) ^ 2)
  ∧ -- (2'') DOUBLING IS FREE: the sign is unchanged, which is what lets an integer-coefficient
    -- gap combination carry a `B` that is only available doubled.
    (∀ D B q a : ℤ, (0 < D * q + 2 * B * a ↔ 0 < 2 * D * q + 2 * (2 * B) * a))
  ∧ -- (3) GAP BOOKKEEPING over the DOUBLED program, budget `m = 2h`, `2^m = 4^h`.
    -- NOTE the arithmetic, which corrects a `2` in the campaign notes: `gap R₀ - gap R₄ = 2A`,
    -- so `D = 2A - 2^h` IS `(gap R₀ - gap R₄) - 2^h` -- no halving is needed for `D`.  Only
    -- `B` is stuck at twice its value, which is why the test is run doubled.
    (∀ (Rc : ℕ → Str × Str → Bool) (z : Str) (h : ℕ) (Nc : ℕ → ℕ),
        (∀ (R : Str × Str → Bool) (y : Str) (m : ℕ), countAccept R y m ≤ 2 ^ m) →
        (∀ d : ℕ, countAccept (Rc d) z (2 * h) = Nc d) →
        (∀ d : ℕ, Nc d ≤ 4 ^ h)
          ∧ (∀ d : ℕ, gap (Rc d) z (2 * h) = 2 * (Nc d : ℤ) - 4 ^ h)
          ∧ gap (Rc 0) z (2 * h) - gap (Rc 4) z (2 * h) = 2 * ((Nc 0 : ℤ) - (Nc 4 : ℤ))
          ∧ gap (Rc 1) z (2 * h) - gap (Rc 3) z (2 * h) = 2 * ((Nc 1 : ℤ) - (Nc 3 : ℤ))
          ∧ ((Nc 1 : ℤ) - (Nc 3 : ℤ)).natAbs ≤ 4 ^ h
          ∧ 2 * ((Nc 0 : ℤ) - (Nc 4 : ℤ)) - 2 ^ h
              = gap (Rc 0) z (2 * h) - gap (Rc 4) z (2 * h) - 2 ^ h
          ∧ 2 * (2 * ((Nc 0 : ℤ) - (Nc 4 : ℤ)) - 2 ^ h)
              = 2 * (gap (Rc 0) z (2 * h) - gap (Rc 4) z (2 * h)) - 2 ^ (h + 1))
  ∧ -- (4) A GAP-POSITIVE CHARACTERISATION IS `PP` MEMBERSHIP, in both the published class and
    -- the relativised one (`PPof PolyTimeChecker` is definitionally `PP`).
    (∀ (L : Language Bool) (Rf : Str × Str → Bool) (k : ℕ),
        PolyTimeChecker Rf →
        (∀ x : Str, x ∈ L ↔ 0 < gap Rf x (x.length ^ k)) →
        L ∈ ShiClassPP.PP ∧ L ∈ ShiClassRel.PPof PvsNP.PolyTimeChecker)
  ∧ -- (5) THE HEADLINE, CONDITIONAL.  A language whose acceptance probability is `ℤ[√2]`-valued
    -- with the `BQP` promise, and for which SOME poly-time checker's gap realises the doubled
    -- integer test at witness length `x.length ^ k`, is in `PP`.
    (∀ (L : Language Bool) (k : ℕ) (hh : Str → ℕ) (Av Bv : Str → ℤ)
        (Rf : Str × Str → Bool),
        PolyTimeChecker Rf →
        (∀ x : Str, (Bv x).natAbs ≤ 4 ^ hh x) →
        (∀ x : Str, x ∈ L →
            (2 : ℝ) / 3 ≤ (1 / 2 : ℝ) ^ hh x
              * ((Av x : ℝ) + (Bv x : ℝ) * Real.sqrt 2)) →
        (∀ x : Str, x ∉ L →
            (1 / 2 : ℝ) ^ hh x * ((Av x : ℝ) + (Bv x : ℝ) * Real.sqrt 2)
              ≤ (1 : ℝ) / 3) →
        (∀ x : Str, gap Rf x (x.length ^ k)
            = 2 * ((2 * Av x - 2 ^ hh x) * 2 ^ (hh x + 3)
                + 2 * Bv x * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ))) →
        L ∈ ShiClassPP.PP ∧ L ∈ ShiClassRel.PPof PvsNP.PolyTimeChecker) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h A B p hp
    exact ⟨shift_id h A B p hp, fun h23 => prom_hi h A B p hp h23,
      fun h13 => prom_lo h A B p hp h13⟩
  · intro h D B q a hq ha0 hs1 hs2 hB hprom
    exact approx_sign h D B q a hq ha0 hs1 hs2 hB hprom
  · intro s
    exact sqrt_bounds s
  · intro D B q a
    constructor <;> intro hh <;> linarith
  · intro Rc z h Nc hcle hcount
    have hNle : ∀ d : ℕ, Nc d ≤ 4 ^ h := by
      intro d
      have h1 := hcle (Rc d) z (2 * h)
      rw [hcount d, two_pow_two_mul h] at h1
      exact h1
    have hgap : ∀ d : ℕ, gap (Rc d) z (2 * h) = 2 * (Nc d : ℤ) - 4 ^ h := by
      intro d
      have h2 : gap (Rc d) z (2 * h) = 2 * (countAccept (Rc d) z (2 * h) : ℤ)
          - (2 : ℤ) ^ (2 * h) := rfl
      rw [h2, hcount d, two_pow_two_mul_int h]
    refine ⟨hNle, hgap, ?_, ?_, natAbs_sub_le (Nc 1) (Nc 3) (4 ^ h) (hNle 1) (hNle 3),
      ?_, ?_⟩
    · rw [hgap 0, hgap 4]; ring
    · rw [hgap 1, hgap 3]; ring
    · rw [hgap 0, hgap 4]; ring
    · rw [hgap 0, hgap 4]; rw [pow_succ]; ring
  · intro L Rf k hpt hiff
    exact ⟨mem_PP_of_gap L Rf k hpt hiff, mem_PPof_of_gap L Rf k hpt hiff⟩
  · intro L k hh Av Bv Rf hpt hBb hin hout hgap
    have hiff : ∀ x : Str, x ∈ L ↔ 0 < gap Rf x (x.length ^ k) := by
      intro x
      obtain ⟨ha0, hs1, hs2⟩ := sqrt_bounds (hh x + 3)
      have hs1' : (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ) ^ 2
          ≤ 2 * ((2 : ℤ) ^ (hh x + 3)) ^ 2 := hs1
      have hs2' : 2 * ((2 : ℤ) ^ (hh x + 3)) ^ 2
          < ((Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ) + 1) ^ 2 := hs2
      have hgx := hgap x
      by_cases hmem : x ∈ L
      · have hprom : (2 : ℝ) ^ hh x / 3
            ≤ ((2 * Av x - 2 ^ hh x : ℤ) : ℝ) + 2 * (Bv x : ℝ) * Real.sqrt 2 :=
          prom_hi (hh x) (Av x) (Bv x) _ rfl (hin x hmem)
        have hsign := approx_sign (hh x) (2 * Av x - 2 ^ hh x) (Bv x)
          ((2 : ℤ) ^ (hh x + 3)) (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)
          rfl ha0 hs1' hs2' (hBb x) (Or.inl hprom)
        have hXpos : (0 : ℝ) < ((2 * Av x - 2 ^ hh x : ℤ) : ℝ)
            + 2 * (Bv x : ℝ) * Real.sqrt 2 := by
          have hu : (0 : ℝ) < (2 : ℝ) ^ hh x := by positivity
          linarith
        have := hsign.mp hXpos
        constructor
        · intro _; rw [hgx]; linarith
        · intro _; exact hmem
      · have hprom : ((2 * Av x - 2 ^ hh x : ℤ) : ℝ) + 2 * (Bv x : ℝ) * Real.sqrt 2
            ≤ -((2 : ℝ) ^ hh x / 3) :=
          prom_lo (hh x) (Av x) (Bv x) _ rfl (hout x hmem)
        have hsign := approx_sign (hh x) (2 * Av x - 2 ^ hh x) (Bv x)
          ((2 : ℤ) ^ (hh x + 3)) (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)
          rfl ha0 hs1' hs2' (hBb x) (Or.inr hprom)
        have hXneg : ¬ ((0 : ℝ) < ((2 * Av x - 2 ^ hh x : ℤ) : ℝ)
            + 2 * (Bv x : ℝ) * Real.sqrt 2) := by
          have hu : (0 : ℝ) < (2 : ℝ) ^ hh x := by positivity
          intro hcon; linarith
        have hnot : ¬ (0 < (2 * Av x - 2 ^ hh x) * (2 : ℤ) ^ (hh x + 3)
            + 2 * Bv x * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)) := fun hcon =>
          hXneg (hsign.mpr hcon)
        constructor
        · intro hcon; exact absurd hcon hmem
        · intro hcon; exfalso; rw [hgx] at hcon; exact hnot (by linarith)
    exact ⟨mem_PP_of_gap L Rf k hpt hiff, mem_PPof_of_gap L Rf k hpt hiff⟩

end BQPReferenceValidation.Source6

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPReferenceValidation.candidate6
    let target ← getConstInfo ``ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership
    unless info.levelParams.length == target.levelParams.length do
      throwError "Universe parameter mismatch: ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership"
    let proofType := info.type.instantiateLevelParams info.levelParams
      (target.levelParams.map Level.param)
    unless ← isDefEq proofType target.type do
      throwError "Proof type mismatch: ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership"
    if (info.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.contains ``sorryAx) then
      throwError "Direct placeholder: ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership"
    let axioms ← collectAxioms ``BQPReferenceValidation.candidate6
    logInfo m!"BQP_REFERENCE_TYPE_CHECKED ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership; axioms {axioms}"
