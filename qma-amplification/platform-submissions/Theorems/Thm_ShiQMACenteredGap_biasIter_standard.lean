import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false

/-- Centered majority bias is the complement of the standard error recurrence. -/
theorem ShiQMACenteredGap.biasIter_standard (r : Nat) :
    ShiQMACenteredGap.biasIter (1 / 6) r =
      1 / 2 - ShiQMAErrorIteration.error r := by
  sorry
