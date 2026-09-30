-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.ccz_phase_exponent_eq`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_ccz_phase_exponent_eq`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem ccz_phase_exponent_eq (a b c : Bool) :
    Complex.exp (Complex.I * Real.pi / 4) ^
        ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
          + 7 * (if xor a b then 1 else 0) + 7 * (if xor b c then 1 else 0)
          + 7 * (if xor a c then 1 else 0) + (if xor a (xor b c) then 1 else 0))
      = if (a && b && c) then (-1 : ℂ) else 1 := by
  sorry

end ShiShallow
