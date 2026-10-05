-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_explicit_combined_checker_and_the_conditional_pp_membership`. The real proof is on prove2.me.
import Definitions.Def_ShiClassPP

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open Finset

namespace ShiBQP

theorem explicit_combined_checker_and_the_conditional_pp_membership :
      -- (H2) `LINCOMBb` conjunct (a): the N-ary split
      (∀ (m n : ℕ) (R : List Bool × List Bool → Bool)
          (F : (Fin n → Bool) → List Bool × List Bool → Bool) (x : List Bool),
          (∀ b : Fin (m + n) → Bool, R (x, List.ofFn b)
            = F (fun j : Fin n => b (Fin.natAdd m j))
                (x, List.ofFn (fun i : Fin m => b (Fin.castAdd n i)))) →
          ShiClassPP.gap R x (m + n) = ∑ v : Fin n → Bool, ShiClassPP.gap (F v) x m) →
      -- (H3) the complement flips the gap
      (∀ (R : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ),
          ShiClassPP.gap (fun p => !(R p)) x m = -ShiClassPP.gap R x m) →
      -- (H4) the first-bit split
      (∀ (R R₁ R₂ : List Bool × List Bool → Bool) (x : List Bool) (m : ℕ),
          (∀ b : Fin (m + 1) → Bool, R (x, List.ofFn b)
            = if b 0 then R₂ (x, List.ofFn (fun i : Fin m => b i.succ))
              else R₁ (x, List.ofFn (fun i : Fin m => b i.succ))) →
          ShiClassPP.gap R x (m + 1) = ShiClassPP.gap R₁ x m + ShiClassPP.gap R₂ x m) →
      -- (1) THE CASE BUDGET FITS: `h + 7` case bits hold every bucket.
      (∀ h : ℕ, 2 * 2 ^ (h + 4) + 4 * Nat.sqrt (2 * 4 ^ (h + 3)) + 16 ≤ 2 ^ (h + 7))
    ∧ -- (2) THE EXPLICIT COMBINED CHECKER and its gap identity.
      (∀ (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
          (Rf : List Bool × List Bool → Bool),
          (∀ (x w : List Bool) (v A S : ℕ),
              v = (w.drop (2 * hh x)).foldr (fun b r => (bif b then 1 else 0) + 2 * r) 0 →
              A = 2 ^ (hh x + 4) → S = Nat.sqrt (2 * 4 ^ (hh x + 3)) →
              Rf (x, w)
                = (if v < A then Rc 0 (x, w.take (2 * hh x))
                  else if v < 2 * A then !(Rc 4 (x, w.take (2 * hh x)))
                  else if v < 2 * A + 2 * S then Rc 1 (x, w.take (2 * hh x))
                  else if v < 2 * A + 4 * S then !(Rc 3 (x, w.take (2 * hh x)))
                  else if v < 2 * A + 4 * S + 16 then false
                  else (w.take (2 * hh x)).headI)) →
          -- (2a) the raw gap identity, at ANY witness length `N ≥ 3 * h + 7`
          (∀ (x : List Bool) (N : ℕ), 1 ≤ hh x → 3 * hh x + 7 ≤ N →
              ShiClassPP.gap Rf x N
                = 2 * ((ShiClassPP.gap (Rc 0) x (2 * hh x)
                          - ShiClassPP.gap (Rc 4) x (2 * hh x) - 2 ^ hh x)
                        * 2 ^ (hh x + 3)
                    + (ShiClassPP.gap (Rc 1) x (2 * hh x) - ShiClassPP.gap (Rc 3) x (2 * hh x))
                        * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)))
        ∧ -- (2b) the consumer's form, in terms of the two integers `Av`, `Bv`
          (∀ (x : List Bool) (k : ℕ) (Av Bv : ℤ), 1 ≤ hh x →
              3 * hh x + 7 ≤ x.length ^ k →
              2 * Av = ShiClassPP.gap (Rc 0) x (2 * hh x) - ShiClassPP.gap (Rc 4) x (2 * hh x) →
              2 * Bv = ShiClassPP.gap (Rc 1) x (2 * hh x) - ShiClassPP.gap (Rc 3) x (2 * hh x) →
              ShiClassPP.gap Rf x (x.length ^ k)
                = 2 * ((2 * Av - 2 ^ hh x) * 2 ^ (hh x + 3)
                    + 2 * Bv * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)))
        ∧ -- (2c) the same, read straight off the four counts
          (∀ (x : List Bool) (k : ℕ) (Nc : ℕ → ℕ), 1 ≤ hh x →
              3 * hh x + 7 ≤ x.length ^ k →
              (∀ d : ℕ, ShiClassPP.countAccept (Rc d) x (2 * hh x) = Nc d) →
              ShiClassPP.gap Rf x (x.length ^ k)
                = 2 * ((2 * ((Nc 0 : ℤ) - (Nc 4 : ℤ)) - 2 ^ hh x) * 2 ^ (hh x + 3)
                    + 2 * ((Nc 1 : ℤ) - (Nc 3 : ℤ))
                        * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)))
        ∧ -- (2d) THE HEADLINE, now conditional ONLY on `PolyTimeChecker Rf`.  Feeding
          -- (2b) into `ASM-CONS` conjunct (5) -- taken here as a hypothesis, since it is
          -- an accepted theorem -- puts `L` in the strict-majority counting class.
          (∀ (L : Language Bool) (k : ℕ) (Av Bv : List Bool → ℤ),
              (∀ (L' : Language Bool) (k' : ℕ) (hh' : List Bool → ℕ)
                  (Av' Bv' : List Bool → ℤ) (Rf' : List Bool × List Bool → Bool),
                  PvsNP.PolyTimeChecker Rf' →
                  (∀ x : List Bool, (Bv' x).natAbs ≤ 4 ^ hh' x) →
                  (∀ x : List Bool, x ∈ L' →
                      (2 : ℝ) / 3 ≤ (1 / 2 : ℝ) ^ hh' x
                        * ((Av' x : ℝ) + (Bv' x : ℝ) * Real.sqrt 2)) →
                  (∀ x : List Bool, x ∉ L' →
                      (1 / 2 : ℝ) ^ hh' x * ((Av' x : ℝ) + (Bv' x : ℝ) * Real.sqrt 2)
                        ≤ (1 : ℝ) / 3) →
                  (∀ x : List Bool, ShiClassPP.gap Rf' x (x.length ^ k')
                      = 2 * ((2 * Av' x - 2 ^ hh' x) * 2 ^ (hh' x + 3)
                          + 2 * Bv' x * (Nat.sqrt (2 * 4 ^ (hh' x + 3)) : ℤ))) →
                  L' ∈ ShiClassPP.PP) →
              PvsNP.PolyTimeChecker Rf →
              (∀ x : List Bool, 1 ≤ hh x) →
              (∀ x : List Bool, 3 * hh x + 7 ≤ x.length ^ k) →
              (∀ x : List Bool, 2 * Av x = ShiClassPP.gap (Rc 0) x (2 * hh x)
                  - ShiClassPP.gap (Rc 4) x (2 * hh x)) →
              (∀ x : List Bool, 2 * Bv x = ShiClassPP.gap (Rc 1) x (2 * hh x)
                  - ShiClassPP.gap (Rc 3) x (2 * hh x)) →
              (∀ x : List Bool, (Bv x).natAbs ≤ 4 ^ hh x) →
              (∀ x : List Bool, x ∈ L →
                  (2 : ℝ) / 3 ≤ (1 / 2 : ℝ) ^ hh x
                    * ((Av x : ℝ) + (Bv x : ℝ) * Real.sqrt 2)) →
              (∀ x : List Bool, x ∉ L →
                  (1 / 2 : ℝ) ^ hh x * ((Av x : ℝ) + (Bv x : ℝ) * Real.sqrt 2)
                    ≤ (1 : ℝ) / 3) →
              L ∈ ShiClassPP.PP))
    ∧ -- (3) NON-VACUITY: the defining equation IS satisfiable, its side conditions ARE
      -- simultaneously satisfiable, the dispatch genuinely reaches two different buckets
      -- with two different answers, and the realised right-hand side is not identically `0`.
      (∃ (hh : List Bool → ℕ) (Rc : ℕ → List Bool × List Bool → Bool)
          (Rf : List Bool × List Bool → Bool) (x : List Bool) (k : ℕ),
          (∀ (x0 w : List Bool) (v A S : ℕ),
              v = (w.drop (2 * hh x0)).foldr (fun b r => (bif b then 1 else 0) + 2 * r) 0 →
              A = 2 ^ (hh x0 + 4) → S = Nat.sqrt (2 * 4 ^ (hh x0 + 3)) →
              Rf (x0, w)
                = (if v < A then Rc 0 (x0, w.take (2 * hh x0))
                  else if v < 2 * A then !(Rc 4 (x0, w.take (2 * hh x0)))
                  else if v < 2 * A + 2 * S then Rc 1 (x0, w.take (2 * hh x0))
                  else if v < 2 * A + 4 * S then !(Rc 3 (x0, w.take (2 * hh x0)))
                  else if v < 2 * A + 4 * S + 16 then false
                  else (w.take (2 * hh x0)).headI))
        ∧ 1 ≤ hh x
        ∧ 3 * hh x + 7 ≤ x.length ^ k
        ∧ Rf (x, [false, false]) = false
        ∧ Rf (x, [false, false, false, false, false, false, false, true]) = true
        ∧ (2 : ℤ) * ((2 * 2 - 2 ^ hh x) * 2 ^ (hh x + 3)
            + 2 * 0 * (Nat.sqrt (2 * 4 ^ (hh x + 3)) : ℤ)) ≠ 0) := by
  sorry

end ShiBQP
