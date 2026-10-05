-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.majority3_accum`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_majority3_accum`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem majority3_accum {n : ℕ} (w0 w1 w2 t : Fin n)
    (hw0t : w0 ≠ t) (hw1t : w1 ≠ t) (hw2t : w2 ≠ t)
    (TOF : Fin n → Fin n → Fin n → QState n → QState n)
    (hTOF : ∀ (p q r : Fin n) (ψ : QState n),
      TOF p q r ψ = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
    (ψ : QState n) :
    TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t ψ))
      = fun x => ψ (Function.update x t
          (xor (xor (xor (x t) (x w0 && x w1)) (x w1 && x w2)) (x w2 && x w0))) := by
  sorry

end ShiShallow
