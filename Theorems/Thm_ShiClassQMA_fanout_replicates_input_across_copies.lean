-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.fanout_replicates_input_across_copies`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_fanout_replicates_input_across_copies`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Theorems.Thm_ShiShallow_runLayered_append_action_readout
import Mathlib.Logic.Basic

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem fanout_replicates_input_across_copies {n : ℕ} (G : QMAFamily) (x : Bits n) (Ψ : QState (G.wit n))
    (p q : Fin n → Fin (G.anc n + 1)) (hpq : ∀ j j' : Fin n, p j ≠ q j')
    (cA cR : Layered (n + (G.wit n + (G.anc n + 1))))
    (uA uR : Bits (n + (G.wit n + (G.anc n + 1))) →
      Bits (n + (G.wit n + (G.anc n + 1))))
    (hA : ∀ Φ : QState (n + (G.wit n + (G.anc n + 1))),
      runLayered cA Φ = fun Y => Φ (uA Y))
    (hR : ∀ Φ : QState (n + (G.wit n + (G.anc n + 1))),
      runLayered cR Φ = fun Y => Φ (uR Y))
    (huA1 : ∀ (Y : Bits (n + (G.wit n + (G.anc n + 1)))) (j : Fin n),
      uA Y (Fin.natAdd n (Fin.natAdd (G.wit n) (p j)))
        = xor (Y (Fin.natAdd n (Fin.natAdd (G.wit n) (p j))))
            (Y (Fin.castAdd (G.wit n + (G.anc n + 1)) j)))
    (huA2 : ∀ (Y : Bits (n + (G.wit n + (G.anc n + 1))))
      (k : Fin (n + (G.wit n + (G.anc n + 1)))),
      (∀ j : Fin n, Fin.natAdd n (Fin.natAdd (G.wit n) (p j)) ≠ k) → uA Y k = Y k)
    (huR1 : ∀ (Y : Bits (n + (G.wit n + (G.anc n + 1)))) (j : Fin n),
      uR Y (Fin.natAdd n (Fin.natAdd (G.wit n) (q j)))
        = xor (Y (Fin.natAdd n (Fin.natAdd (G.wit n) (q j))))
            (Y (Fin.castAdd (G.wit n + (G.anc n + 1)) j)))
    (huR2 : ∀ (Y : Bits (n + (G.wit n + (G.anc n + 1))))
      (k : Fin (n + (G.wit n + (G.anc n + 1)))),
      (∀ j : Fin n, Fin.natAdd n (Fin.natAdd (G.wit n) (q j)) ≠ k) → uR Y k = Y k) :
    runLayered (cA ++ cR) (witnessInputState G x Ψ)
      = fun Y =>
          if (∀ i : Fin n, Y (Fin.castAdd (G.wit n + (G.anc n + 1)) i) = x i)
              ∧ (∀ j : Fin n, Y (Fin.natAdd n (Fin.natAdd (G.wit n) (p j))) = x j)
              ∧ (∀ j : Fin n, Y (Fin.natAdd n (Fin.natAdd (G.wit n) (q j))) = x j)
              ∧ (∀ l : Fin (G.anc n + 1), (∀ j : Fin n, p j ≠ l) →
                  (∀ j : Fin n, q j ≠ l) →
                  Y (Fin.natAdd n (Fin.natAdd (G.wit n) l)) = false)
          then Ψ (fun w : Fin (G.wit n) => Y (Fin.natAdd n (Fin.castAdd (G.anc n + 1) w)))
          else 0 := by
  sorry

end ShiClassQMA
