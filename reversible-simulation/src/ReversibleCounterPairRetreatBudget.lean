import ReversibleCounterPairRetreat

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- The actual decrement traversal never increases a counter. -/
theorem counterPairRetreatTemplate_budget (a b remaining : R) (hab : a ≠ b)
    (ha : a ≠ remaining) (hb : b ≠ remaining) (cs : R → Nat) (B : Nat)
    (hbound : ∀ q,cs q ≤ B) : ∀ q,(counterPairRetreatTemplate a b remaining).counters cs q ≤ B := by
  intro q
  have hqa := hbound a
  have hqb := hbound b
  have hq := hbound q
  rw [counterPairRetreatTemplate_counters a b remaining hab ha hb]
  simp only [Function.update_apply]
  split_ifs <;> omega

end ShiReversibleGenerator
