-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.tensor_majority_three_accept_weight_closed_form`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_tensor_majority_three_accept_weight_closed_form`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem tensor_majority_three_accept_weight_closed_form (M P Q : ℕ) (p : ℝ)
    (ψ : QState M) (φ : QState P) (χ : QState Q)
    (f : Bits M → Bool) (g : Bits P → Bool) (h : Bits Q → Bool)
    (hJoint : ∀ (m n : ℕ) (a : QState m) (b : QState n)
      (u : Bits m → Bool) (v : Bits n → Bool),
      ∑ y : Bits (m + n), (if u (leftBits y) && v (rightBits y)
          then ‖tensor a b y‖ ^ 2 else 0)
        = (∑ s : Bits m, (if u s then ‖a s‖ ^ 2 else 0))
          * ∑ t : Bits n, (if v t then ‖b t‖ ^ 2 else 0))
    (hIE : ∀ b1 b2 b3 : Bool,
      (if 2 ≤ (if b1 then (1 : ℕ) else 0) + (if b2 then (1 : ℕ) else 0)
            + (if b3 then (1 : ℕ) else 0) then (1 : ℝ) else 0)
        = (if b1 then (1 : ℝ) else 0) * (if b2 then (1 : ℝ) else 0)
          + (if b2 then (1 : ℝ) else 0) * (if b3 then (1 : ℝ) else 0)
          + (if b3 then (1 : ℝ) else 0) * (if b1 then (1 : ℝ) else 0)
          - 2 * ((if b1 then (1 : ℝ) else 0) * (if b2 then (1 : ℝ) else 0)
              * (if b3 then (1 : ℝ) else 0)))
    (hfp : ∑ a : Bits M, (if f a then ‖ψ a‖ ^ 2 else 0) = p)
    (hgp : ∑ b : Bits P, (if g b then ‖φ b‖ ^ 2 else 0) = p)
    (hhp : ∑ c : Bits Q, (if h c then ‖χ c‖ ^ 2 else 0) = p)
    (hψ1 : ∑ a : Bits M, ‖ψ a‖ ^ 2 = 1)
    (hφ1 : ∑ b : Bits P, ‖φ b‖ ^ 2 = 1)
    (hχ1 : ∑ c : Bits Q, ‖χ c‖ ^ 2 = 1) :
    ∑ y : Bits (M + (P + Q)),
      (if 2 ≤ (if f (leftBits y) then (1 : ℕ) else 0)
            + (if g (leftBits (rightBits y)) then (1 : ℕ) else 0)
            + (if h (rightBits (rightBits y)) then (1 : ℕ) else 0)
        then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0)
      = 3 * p ^ 2 - 2 * p ^ 3 := by
  sorry

end ShiTensor
