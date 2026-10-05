-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassPP_majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings`. The real proof is on prove2.me.
import Definitions.Def_ShiClassPP

set_option autoImplicit false
set_option maxHeartbeats 1600000

open PvsNP ShiClassPP

namespace ShiClassPP

theorem majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings :
    -- (1) at witness length `0` there is exactly ONE witness, the empty one.
    (∀ (R : Str × Str → Bool) (x : Str),
        countAccept R x 0 = if R (x, []) = true then 1 else 0)
    -- (2) at witness length `1` there are exactly TWO.
  ∧ (∀ (R : Str × Str → Bool) (x : Str),
        countAccept R x 1
          = (if R (x, [true]) = true then 1 else 0)
            + (if R (x, [false]) = true then 1 else 0))
    -- (3) the `PP` majority condition at `m = 0`.
  ∧ (∀ (R : Str × Str → Bool) (x : Str),
        (2 * countAccept R x 0 > 2 ^ 0 ↔ R (x, []) = true))
    -- (4) the `PP` majority condition at `m = 1` -- BOTH witnesses must accept.
  ∧ (∀ (R : Str × Str → Bool) (x : Str),
        (2 * countAccept R x 1 > 2 ^ 1
          ↔ (R (x, [false]) = true ∧ R (x, [true]) = true)))
    -- (5) a checker constant in the witness decides the majority condition at EVERY `m`.
  ∧ (∀ (R : Str × Str → Bool) (x : Str) (c : Bool) (m : ℕ), (∀ w : Str, R (x, w) = c) →
        (2 * countAccept R x m > 2 ^ m ↔ c = true))
    -- (6) TOP-LEVEL GLUE: correctness on inputs of length `≥ 2` plus the three short
    -- strings gives `PP` membership.  `PolyTimeChecker R` is a HYPOTHESIS.
  ∧ (∀ (L : Language Bool) (R : Str × Str → Bool) (k : ℕ), 1 ≤ k → PolyTimeChecker R →
        (∀ x : Str, 2 ≤ x.length →
          (x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k))) →
        ([] ∈ L ↔ R ([], []) = true) →
        ([false] ∈ L ↔ (R ([false], [false]) = true ∧ R ([false], [true]) = true)) →
        ([true] ∈ L ↔ (R ([true], [false]) = true ∧ R ([true], [true]) = true)) →
        L ∈ PP)
    -- (7) the same, in the form a checker patched to CONSTANTS on the three short strings
    -- delivers.
  ∧ (∀ (L : Language Bool) (R : Str × Str → Bool) (k : ℕ) (c₀ c₁ c₂ : Bool),
        1 ≤ k → PolyTimeChecker R →
        (∀ x : Str, 2 ≤ x.length →
          (x ∈ L ↔ 2 * countAccept R x (x.length ^ k) > 2 ^ (x.length ^ k))) →
        (∀ w : Str, R ([], w) = c₀) → (∀ w : Str, R ([false], w) = c₁) →
        (∀ w : Str, R ([true], w) = c₂) →
        (c₀ = true ↔ [] ∈ L) → (c₁ = true ↔ [false] ∈ L) → (c₂ = true ↔ [true] ∈ L) →
        L ∈ PP) := by
  sorry

end ShiClassPP
