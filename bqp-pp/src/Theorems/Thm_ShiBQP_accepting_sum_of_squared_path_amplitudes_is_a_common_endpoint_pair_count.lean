-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count`. The real proof is on prove2.me.
import Definitions.Def_ShiClassRel

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ShiBQP

theorem accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count :
    ∀ (Om io : Type) [Fintype Om] [DecidableEq Om] [Fintype io] [DecidableEq io]
      (acc : Om → Bool) (h : ℕ) (kk : io → ℕ) (Y : io → Om) (amp : Om → ℂ) (om : ℂ)
      (P : Om → ℕ → ℕ) (C : ℕ → ℕ),
      -- the within-fibre ordered pair counts, graded by phase difference mod 8
      (∀ (y : Om) (d : ℕ), P y d = (Finset.univ.filter
          (fun q : io × io => Y q.1 = y ∧ Y q.2 = y
            ∧ (kk q.1 + 8 - kk q.2 % 8) % 8 = d)).card) →
      -- the global count: a COMMON endpoint, which must be accepting
      (∀ d : ℕ, C d = (Finset.univ.filter
          (fun q : io × io => acc (Y q.1) = true ∧ Y q.1 = Y q.2
            ∧ (kk q.1 + 8 - kk q.2 % 8) % 8 = d)).card) →
      -- COUNT-1 conjunct (0): the path-sum prefactor contributes exactly `(1/2)^h`
      (∀ (n : ℕ) (z : ℂ),
          ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ n * z‖ ^ 2 = (1 / 2 : ℝ) ^ n * ‖z‖ ^ 2) →
      -- the path sum, fibred over the output string
      (∀ y : Om, amp y = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ h
          * ∑ i ∈ Finset.univ.filter (fun i : io => Y i = y), om ^ kk i) →
      -- RING-1 conjunct (2), applied fibrewise
      (∀ y : Om, ‖∑ i ∈ Finset.univ.filter (fun i : io => Y i = y), om ^ kk i‖ ^ 2
          = ((P y 0 : ℝ) - (P y 4 : ℝ))
            + Real.sqrt 2 * ((P y 1 : ℝ) - (P y 3 : ℝ))) →
      -- (A) THE FIBRE PARTITION
      (∀ d : ℕ, ∑ y ∈ Finset.univ.filter (fun y : Om => acc y = true), P y d = C d)
      -- (B) THE CONSUMER IDENTITY, in `acceptProb`'s own shape
      ∧ (∑ y : Om, (if acc y = true then ‖amp y‖ ^ 2 else 0))
          = (1 / 2 : ℝ) ^ h * (((C 0 : ℝ) - (C 4 : ℝ))
              + Real.sqrt 2 * ((C 1 : ℝ) - (C 3 : ℝ))) := by
  sorry

end ShiBQP
