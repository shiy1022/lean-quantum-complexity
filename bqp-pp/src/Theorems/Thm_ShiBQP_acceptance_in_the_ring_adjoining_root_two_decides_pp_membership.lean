-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_acceptance_in_the_ring_adjoining_root_two_decides_pp_membership`. The real proof is on prove2.me.
import Definitions.Def_ShiClassRel

set_option autoImplicit false
set_option maxHeartbeats 1600000

open ShiClassPP PvsNP

namespace ShiBQP

theorem acceptance_in_the_ring_adjoining_root_two_decides_pp_membership :
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
  sorry

end ShiBQP
