-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.acceptWith_eq_majority_weight_before_readout`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_acceptWith_eq_majority_weight_before_readout`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Theorems.Thm_ShiShallow_runLayered_append_action_readout
import Theorems.Thm_ShiShallow_majority3_accum
import Theorems.Thm_ShiShallow_majority_readout_scratch_accept_weight_eq_majority_weight

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem acceptWith_eq_majority_weight_before_readout {n : ℕ} (G : QMAFamily) (x : Bits n) (Psi : QState (G.wit n))
    (cA rd : Layered (n + (G.wit n + (G.anc n + 1))))
    (w1 w2 w3 : Fin (n + (G.wit n + (G.anc n + 1))))
    (h1 : w1 ≠ G.out n) (h2 : w2 ≠ G.out n) (h3 : w3 ≠ G.out n)
    (hcirc : G.circ n = cA ++ rd)
    (hrd : ∀ ψ : QState (n + (G.wit n + (G.anc n + 1))),
      runLayered rd ψ
        = fun z => ψ (Function.update z (G.out n)
            (xor (z (G.out n))
              (xor (xor (z w1 && z w2) (z w2 && z w3)) (z w1 && z w3)))))
    (hInit : ∀ z : Bits (n + (G.wit n + (G.anc n + 1))),
      z (G.out n) = true → runLayered cA (witnessInputState G x Psi) z = 0) :
    G.acceptWith x Psi
      = ∑ z : Bits (n + (G.wit n + (G.anc n + 1))),
          (if z (G.out n) = false ∧ (2 : ℕ) ≤ (if z w1 then (1 : ℕ) else 0)
                + (if z w2 then (1 : ℕ) else 0) + (if z w3 then (1 : ℕ) else 0)
            then ‖runLayered cA (witnessInputState G x Psi) z‖ ^ 2 else 0) := by
  sorry

end ShiClassQMA
