-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.majority_readout_scratch_accept_weight_eq_majority_weight`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_majority_readout_scratch_accept_weight_eq_majority_weight`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem majority_readout_scratch_accept_weight_eq_majority_weight {n : ℕ}
    (w0 w1 w2 t : Fin n) (h0 : w0 ≠ t) (h1 : w1 ≠ t) (h2 : w2 ≠ t)
    (ψ : QState n)
    (hInit : ∀ z : Bits n, z t = true → ψ z = 0)
    (TOF : Fin n → Fin n → Fin n → QState n → QState n)
    (hRead : ∀ φ : QState n,
      TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t φ))
        = fun x : Bits n => φ (Function.update x t
            (xor (xor (xor (x t) (x w0 && x w1)) (x w1 && x w2)) (x w2 && x w0))))
    (hMaj : ∀ a b c : Bool,
      xor (xor (a && b) (b && c)) (c && a)
        = (if (2 : ℕ) ≤ (if a then (1 : ℕ) else 0) + (if b then (1 : ℕ) else 0)
            + (if c then (1 : ℕ) else 0) then true else false)) :
    (∑ y : Bits n, (if y t = true then
        ‖TOF w2 w0 t (TOF w1 w2 t (TOF w0 w1 t ψ)) y‖ ^ 2 else 0))
      = ∑ z : Bits n, (if z t = false ∧ (2 : ℕ) ≤ (if z w0 then (1 : ℕ) else 0)
          + (if z w1 then (1 : ℕ) else 0) + (if z w2 then (1 : ℕ) else 0)
          then ‖ψ z‖ ^ 2 else 0) := by
  sorry

end ShiShallow
