-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassPP.gap_general_integer_linear_combination`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassPP_gap_general_integer_linear_combination`. The real proof is on prove2.me.
import Definitions.Def_ShiClassPP

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

open PvsNP

namespace ShiClassPP

theorem gap_general_integer_linear_combination :
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
  sorry

end ShiClassPP
