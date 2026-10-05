-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ShiBQP

theorem modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two :
    (∀ ω : ℂ, ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4) →
        ω ^ 8 = 1 ∧ ω ^ 4 = -1 ∧ ‖ω‖ = 1 ∧ ω ^ 2 = Complex.I ∧
          ω + ω ^ 7 = ((Real.sqrt 2 : ℝ) : ℂ) ∧
          2 * Real.cos (Real.pi / 4) = Real.sqrt 2) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (ω : ℂ),
        ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4) →
        (∑ i, ω ^ k i
            = ∑ j ∈ Finset.range 8,
                (((Finset.univ.filter (fun i => k i % 8 = j)).card : ℕ) : ℂ) * ω ^ j) ∧
        (((‖∑ i, ω ^ k i‖ ^ 2 : ℝ) : ℂ)
            = ∑ d ∈ Finset.range 8,
                (((Finset.univ.filter
                    (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = d)).card : ℕ) : ℂ)
                  * ω ^ d) ∧
        (∀ d : ℕ, d ≠ 0 → d < 8 →
            (Finset.univ.filter
                (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 8 - d)).card
              = (Finset.univ.filter
                (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = d)).card) ∧
        ‖∑ i, ω ^ k i‖ ^ 2
            = (((Finset.univ.filter
                  (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 0)).card : ℕ) : ℝ)
              - (((Finset.univ.filter
                  (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 4)).card : ℕ) : ℝ)
              + Real.sqrt 2
                * ((((Finset.univ.filter
                      (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 1)).card : ℕ) : ℝ)
                  - (((Finset.univ.filter
                      (fun p : ι × ι => (k p.1 + 8 - k p.2 % 8) % 8 = 3)).card : ℕ) : ℝ))) ∧
    (∀ ω : ℂ, ω = Complex.exp (Complex.I * (Real.pi : ℂ) / 4) →
        ((Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 1)).card = 1 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 3)).card = 0 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 0)).card = 2 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 => ((p.1 : ℕ) + 8 - (p.2 : ℕ) % 8) % 8 = 4)).card = 0 ∧
            ‖∑ i : Fin 2, ω ^ (i : ℕ)‖ ^ 2 = 2 + Real.sqrt 2 ∧
            (2 : ℝ) + Real.sqrt 2 ≠ 2) ∧
        ((∑ i : Fin 2, ω ^ (4 * (i : ℕ))) = 0 ∧
            ‖∑ i : Fin 2, ω ^ (4 * (i : ℕ))‖ ^ 2 = 0 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 0)).card = 2 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 4)).card = 2 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 1)).card = 0 ∧
            (Finset.univ.filter
              (fun p : Fin 2 × Fin 2 =>
                (4 * (p.1 : ℕ) + 8 - 4 * (p.2 : ℕ) % 8) % 8 = 3)).card = 0) ∧
        (‖∑ _i : Fin 3, ω ^ 3‖ ^ 2 = 9 ∧
            (Finset.univ.filter
              (fun _p : Fin 3 × Fin 3 => (3 + 8 - 3 % 8) % 8 = 0)).card = 9)) := by
  sorry

end ShiBQP
