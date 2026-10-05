-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion`. The real proof is on prove2.me.
import Definitions.Def_ShiBQP_Core
import Definitions.Def_ShiClassPP

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ShiBQP

theorem acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion :
    -- (0) the path-sum prefactor contributes exactly `(1/2)^h` to each squared amplitude
    (∀ (h : ℕ) (z : ℂ),
        ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h * z‖ ^ 2 = (1 / 2 : ℝ) ^ h * ‖z‖ ^ 2) ∧
    -- (1) acceptance is `(1/2)^h * (A + B √2)`, `A`, `B` sums of the per-output integers
    (∀ (F : ShiClass.Family) (n : ℕ) (x : ShiShallow.Bits n) (h : ℕ)
        (Z : ShiShallow.Bits (n + (F.anc n + 1)) → ℂ)
        (a b : ShiShallow.Bits (n + (F.anc n + 1)) → ℤ),
        (∀ y, ShiShallow.runLayered (F.circ n) (ShiShallow.inputState (m := F.anc n + 1) x) y
            = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h * Z y) →
        (∀ y, ‖Z y‖ ^ 2 = ((a y : ℤ) : ℝ) + ((b y : ℤ) : ℝ) * Real.sqrt 2) →
        F.accept n x = (1 / 2 : ℝ) ^ h *
          (((∑ y ∈ Finset.univ.filter (fun y => y (F.out n) = true), a y : ℤ) : ℝ)
            + ((∑ y ∈ Finset.univ.filter (fun y => y (F.out n) = true), b y : ℤ) : ℝ)
              * Real.sqrt 2)) ∧
    -- (2) the crux: the irrational comparison reduced to integer arithmetic
    (∀ D B : ℤ,
        ((0 : ℝ) < (D : ℝ) + 2 * (B : ℝ) * Real.sqrt 2 ↔
          ((0 < D ∧ 0 ≤ B) ∨ (0 ≤ D ∧ 0 < B) ∨ (D < 0 ∧ 0 < B ∧ D ^ 2 < 8 * B ^ 2) ∨
            (0 < D ∧ B < 0 ∧ 8 * B ^ 2 < D ^ 2)))) ∧
    (∀ Crit : ℤ → ℤ → Prop,
      (∀ D B : ℤ, (Crit D B ↔
          ((0 < D ∧ 0 ≤ B) ∨ (0 ≤ D ∧ 0 < B) ∨ (D < 0 ∧ 0 < B ∧ D ^ 2 < 8 * B ^ 2) ∨
            (0 < D ∧ B < 0 ∧ 8 * B ^ 2 < D ^ 2)))) →
      -- (2a) the criterion is exactly the `1/2` threshold on the acceptance probability
      ((∀ (h : ℕ) (A B : ℤ) (p : ℝ),
          p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2) →
          ((1 : ℝ) / 2 < p ↔ Crit (2 * A - 2 ^ h) B)) ∧
      -- (2b) it is decidable: a Boolean function on the integers computes it
        (∃ f : ℤ → ℤ → Bool, ∀ D B : ℤ, (Crit D B ↔ f D B = true)) ∧
      -- (2c) with no `√2` part it is exactly the sign test behind `gap`
        (∀ D : ℤ, (Crit D 0 ↔ 0 < D)) ∧
      -- (3) robustness: the BQP gap keeps the comparison away from the boundary
        (∀ (h : ℕ) (A B : ℤ) (p : ℝ),
          p = (1 / 2 : ℝ) ^ h * ((A : ℝ) + (B : ℝ) * Real.sqrt 2) →
          (((2 : ℝ) / 3 ≤ p → Crit (2 * A - 2 ^ h) B) ∧
            (p ≤ (1 : ℝ) / 3 → ¬ Crit (2 * A - 2 ^ h) B))) ∧
      -- (4) the `2 * count - 2 ^ m` shape of `gap`, ready for `mem_ppof_iff_gap_pos`
        (∀ (R : PvsNP.Str × PvsNP.Str → Bool) (x : PvsNP.Str) (m : ℕ),
          (0 < ShiClassPP.gap R x m ↔ 2 ^ m < 2 * ShiClassPP.countAccept R x m)) ∧
      -- (NV1) `√2` flips a NEGATIVE integer verdict to positive: `h = 1`, `A = 1`, `B = 1`
        (¬ ((1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * Real.sqrt 2))
          ∧ (1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((1 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * Real.sqrt 2)
          ∧ Crit (2 * 1 - 2 ^ (1 : ℕ)) 1) ∧
      -- (NV2) `√2` flips a POSITIVE integer verdict to negative: `h = 1`, `A = 2`, `B = -1`
        ((1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((2 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * Real.sqrt 2)
          ∧ ¬ ((1 : ℝ) / 2 <
                (1 / 2 : ℝ) ^ (1 : ℕ) * (((2 : ℤ) : ℝ) + ((-1 : ℤ) : ℝ) * Real.sqrt 2))
          ∧ ¬ Crit (2 * 2 - 2 ^ (1 : ℕ)) (-1)) ∧
      -- (NV3) sanity, no `√2` part: `h = 1`, `A = 2`, `B = 0`
        ((1 : ℝ) / 2 < (1 / 2 : ℝ) ^ (1 : ℕ) * (((2 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * Real.sqrt 2)
          ∧ Crit (2 * 2 - 2 ^ (1 : ℕ)) 0))) := by
  sorry

end ShiBQP
