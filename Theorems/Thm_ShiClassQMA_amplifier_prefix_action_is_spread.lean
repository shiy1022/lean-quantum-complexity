-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.amplifier_prefix_action_is_spread`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_amplifier_prefix_action_is_spread`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiSpread_Core
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiShallow_exists_layout_bijection
import Theorems.Thm_ShiClassQMA_exists_amplifier_three_block_embedding
import Theorems.Thm_ShiClassQMA_fanout_replicates_input_across_copies
import Theorems.Thm_ShiEmbed_embedCirc_depth_append_comp
import Theorems.Thm_ShiSpread_runLayered_embedCirc_spread

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem amplifier_prefix_action_is_spread (T : QMAFamily → QMAFamily)
    (hwit : ∀ (F : QMAFamily) (n : ℕ), (T F).wit n = 3 * F.wit n)
    (hanc : ∀ (F : QMAFamily) (n : ℕ), (T F).anc n = 2 * n + 3 * F.anc n + 3)
    (hout : ∀ (F : QMAFamily) (n : ℕ),
        ((T F).out n).val = 3 * n + 3 * F.wit n + 3 * F.anc n + 3) :
    ∀ (F : QMAFamily) (n : ℕ) (x : Bits n) (Ψ : QState ((T F).wit n))
      (σ : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1) → Fin (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))))
      (p q : Fin n → Fin ((T F).anc n + 1))
      (e1 e2 e3 : Fin (n + (F.wit n + (F.anc n + 1))) → Fin (n + ((T F).wit n + ((T F).anc n + 1))))
      (fan2 fan3 : Layered (n + ((T F).wit n + ((T F).anc n + 1))))
      (u2 u3 : Bits (n + ((T F).wit n + ((T F).anc n + 1))) → Bits (n + ((T F).wit n + ((T F).anc n + 1))))
      (he1 : Function.Injective e1) (he2 : Function.Injective e2)
      (he3 : Function.Injective e3),
      σ = Classical.choose (exists_layout_bijection n (F.wit n) (F.anc n)) →
      (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
          u.val = v.val → (e1 v).val = (σ u).val) →
      (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
          u.val = n + (F.wit n + (F.anc n + 1)) + v.val → (e2 v).val = (σ u).val) →
      (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
          u.val = 2 * (n + (F.wit n + (F.anc n + 1))) + v.val → (e3 v).val = (σ u).val) →
      (∀ j : Fin n, (p j).val = F.anc n + 1 + j.val) →
      (∀ j : Fin n, (q j).val = n + 2 * F.anc n + 2 + j.val) →
      (∀ j j' : Fin n, p j ≠ q j') →
      (∀ Φ : QState (n + ((T F).wit n + ((T F).anc n + 1))), runLayered fan2 Φ = fun Y => Φ (u2 Y)) →
      (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (j : Fin n),
          u2 Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (p j)))
            = xor (Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (p j))))
                (Y (Fin.castAdd ((T F).wit n + ((T F).anc n + 1)) j))) →
      (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (k : Fin (n + ((T F).wit n + ((T F).anc n + 1)))),
          (∀ j : Fin n, Fin.natAdd n (Fin.natAdd ((T F).wit n) (p j)) ≠ k) →
          u2 Y k = Y k) →
      (∀ Φ : QState (n + ((T F).wit n + ((T F).anc n + 1))), runLayered fan3 Φ = fun Y => Φ (u3 Y)) →
      (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (j : Fin n),
          u3 Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (q j)))
            = xor (Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (q j))))
                (Y (Fin.castAdd ((T F).wit n + ((T F).anc n + 1)) j))) →
      (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (k : Fin (n + ((T F).wit n + ((T F).anc n + 1)))),
          (∀ j : Fin n, Fin.natAdd n (Fin.natAdd ((T F).wit n) (q j)) ≠ k) →
          u3 Y k = Y k) →
      ∃ e : Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))) + (n + (F.wit n + (F.anc n + 1)))) → Fin (n + ((T F).wit n + ((T F).anc n + 1))),
        Function.Injective e
        ∧ (∀ v : Fin (n + (F.wit n + (F.anc n + 1))), e (Fin.castAdd (n + (F.wit n + (F.anc n + 1))) (Fin.castAdd (n + (F.wit n + (F.anc n + 1))) v)) = e1 v)
        ∧ (∀ v : Fin (n + (F.wit n + (F.anc n + 1))), e (Fin.castAdd (n + (F.wit n + (F.anc n + 1))) (Fin.natAdd (n + (F.wit n + (F.anc n + 1))) v)) = e2 v)
        ∧ (∀ v : Fin (n + (F.wit n + (F.anc n + 1))), e (Fin.natAdd (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))) v) = e3 v)
        ∧ (∀ k : Fin (n + ((T F).wit n + ((T F).anc n + 1))), ShiSpread.OffImage e k ↔ k = (T F).out n)
        ∧ (∀ (ψ : QState (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))) + (n + (F.wit n + (F.anc n + 1))))) (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))),
            Y ((T F).out n) = true → ShiSpread.spread e ψ Y = 0)
        ∧ runLayered
            (fan2 ++ fan3
              ++ ShiEmbed.embedCirc e1 he1 (F.circ n)
              ++ ShiEmbed.embedCirc e2 he2 (F.circ n)
              ++ ShiEmbed.embedCirc e3 he3 (F.circ n))
            (witnessInputState (T F) x Ψ)
          = ShiSpread.spread e
              (runLayered
                (ShiEmbed.embedCirc
                    ((Fin.castAdd (n + (F.wit n + (F.anc n + 1))) : Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))) → Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))) + (n + (F.wit n + (F.anc n + 1))))) ∘
                      (Fin.castAdd (n + (F.wit n + (F.anc n + 1))) : Fin (n + (F.wit n + (F.anc n + 1))) → Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))))))
                    ((Fin.castAdd_injective (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))) (n + (F.wit n + (F.anc n + 1)))).comp
                      (Fin.castAdd_injective (n + (F.wit n + (F.anc n + 1))) (n + (F.wit n + (F.anc n + 1))))) (F.circ n)
                  ++ ShiEmbed.embedCirc
                    ((Fin.castAdd (n + (F.wit n + (F.anc n + 1))) : Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))) → Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))) + (n + (F.wit n + (F.anc n + 1))))) ∘
                      (Fin.natAdd (n + (F.wit n + (F.anc n + 1))) : Fin (n + (F.wit n + (F.anc n + 1))) → Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))))))
                    ((Fin.castAdd_injective (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))) (n + (F.wit n + (F.anc n + 1)))).comp
                      (Fin.natAdd_injective (n + (F.wit n + (F.anc n + 1))) (n + (F.wit n + (F.anc n + 1))))) (F.circ n)
                  ++ ShiEmbed.embedCirc
                    (Fin.natAdd (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))) :
                      Fin (n + (F.wit n + (F.anc n + 1))) → Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))) + (n + (F.wit n + (F.anc n + 1)))))
                    (Fin.natAdd_injective (n + (F.wit n + (F.anc n + 1))) (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))))) (F.circ n))
                (fun Z : Bits (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))) + (n + (F.wit n + (F.anc n + 1)))) =>
                  if ((∀ i : Fin n, ShiTensor.leftBits (ShiTensor.leftBits Z)
                          (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i)
                        ∧ (∀ l : Fin (F.anc n + 1), ShiTensor.leftBits (ShiTensor.leftBits Z)
                          (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false))
                      ∧ ((∀ i : Fin n, ShiTensor.rightBits (ShiTensor.leftBits Z)
                          (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i)
                        ∧ (∀ l : Fin (F.anc n + 1), ShiTensor.rightBits (ShiTensor.leftBits Z)
                          (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false))
                      ∧ ((∀ i : Fin n, ShiTensor.rightBits Z
                          (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i)
                        ∧ (∀ l : Fin (F.anc n + 1), ShiTensor.rightBits Z
                          (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false))
                  then Ψ (fun j : Fin ((T F).wit n) =>
                    if h : j.val < F.wit n then
                      ShiTensor.leftBits (ShiTensor.leftBits Z)
                        (Fin.natAdd n (Fin.castAdd (F.anc n + 1)
                          (⟨j.val, h⟩ : Fin (F.wit n))))
                    else if h2 : j.val < F.wit n + F.wit n then
                      ShiTensor.rightBits (ShiTensor.leftBits Z)
                        (Fin.natAdd n (Fin.castAdd (F.anc n + 1)
                          (⟨j.val - F.wit n, by omega⟩ : Fin (F.wit n))))
                    else
                      ShiTensor.rightBits Z
                        (Fin.natAdd n (Fin.castAdd (F.anc n + 1)
                          (⟨j.val - F.wit n - F.wit n, by
                            have hj := j.isLt
                            have hw := hwit F n
                            omega⟩ : Fin (F.wit n)))))
                  else 0)) := by
  sorry

end ShiClassQMA
