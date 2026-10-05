-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.string_level_compiler_output_budget_for_any_parser_pair`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_string_level_compiler_output_budget_for_any_parser_pair`. The real proof is on prove2.me.
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Flatten
import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace ShiBQP

theorem string_level_compiler_output_budget_for_any_parser_pair :
    -- (1) `COMPILE-STRd` (7), ∀-QUANTIFIED IN THE PARSER PAIR under its own conjuncts (1) and
    -- (3) as explicit hypotheses.  Those two budgets are the only properties of `unpack` and
    -- `pl` the bound uses, so any consumer's concrete parser reaches the conclusion.
    (∀ (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ)
        (enc : List ℕ → List Bool) (L E : List Bool → List ℕ)
        (r rA : List ℕ → List ℕ) (s x : List Bool) (anc out nl : ℕ) (rest : List ℕ),
      (∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length) →
      (∀ (k : ℕ) (ts : List ℕ),
        ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
          ≤ ts.sum + ts.length) →
      (∀ P : List ℕ, (enc P).length = 4 * P.length) →
      (∀ l : List Bool, (L l).length ≤ 2 * l.length) →
      (∀ l : List Bool, (E l).length ≤ 4 * l.length) →
      (∀ d : List ℕ, (r d).length ≤ 2 * (d.sum + d.length)) →
      (∀ d : List ℕ, (rA d).length ≤ 2 * (d.sum + d.length)) →
      unpack s = anc :: out :: nl :: rest →
      (enc (L (x ++ List.replicate (anc + 1) false)
          ++ (List.replicate (x.length + (anc + 1)) 0
          ++ ((((pl nl rest).1).map r).flatten
          ++ ((List.replicate out 1 ++ ([8] ++ List.replicate out 0))
          ++ (((((pl nl rest).1).reverse).map rA).flatten
          ++ (E (x ++ List.replicate (anc + 1) false)
            ++ List.replicate (x.length + (anc + 1)) 0))))))).length
        ≤ 56 * (s.length + x.length + 1))
    -- (2) NON-VACUITY: a concrete fuelled parser pair meeting both budget hypotheses, with a
    -- computed value that is not the degenerate one.
    ∧ (∃ (unpack : List Bool → List ℕ) (pl : ℕ → List ℕ → List (List ℕ) × List ℕ),
        (∀ w : List Bool, (unpack w).sum + (unpack w).length ≤ w.length)
      ∧ (∀ (k : ℕ) (ts : List ℕ),
          ((pl k ts).1.map List.sum).sum + ((pl k ts).1.map List.length).sum
            ≤ ts.sum + ts.length)
      ∧ unpack [true, true, false, true, false] = [2, 1]
      ∧ (unpack [true, true, false, true, false]).sum
          + (unpack [true, true, false, true, false]).length = 5) := by
  sorry

end ShiBQP
