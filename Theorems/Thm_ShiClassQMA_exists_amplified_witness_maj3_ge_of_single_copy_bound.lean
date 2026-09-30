-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.exists_amplified_witness_maj3_ge_of_single_copy_bound`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_exists_amplified_witness_maj3_ge_of_single_copy_bound`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiSpread_Core
import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiShallow_exists_layout_bijection
import Theorems.Thm_ShiShallow_exists_fanout_embedded_pullback
import Theorems.Thm_ShiShallow_exists_width_cast_reindexing_isometry
import Theorems.Thm_ShiShallow_ofReal_norm_sq
import Theorems.Thm_ShiShallow_runLayered_eq_circMatrix_mulVec
import Theorems.Thm_ShiShallow_circMatrix_unitary
import Theorems.Thm_ShiShallow_apply1_eq_apply1Matrix_mulVec
import Theorems.Thm_ShiShallow_cnotState_eq_cnotMatrix_mulVec
import Theorems.Thm_ShiClassQMA_exists_witnessInputState_isometry
import Theorems.Thm_ShiClassQMA_amplifier_prefix_action_is_spread
import Theorems.Thm_ShiClassQMA_acceptWith_eq_majority_weight_before_readout
import Theorems.Thm_ShiSpread_sum_spread_reindex_of_injective
import Theorems.Thm_ShiTensor_sum_split_factor
import Theorems.Thm_ShiTensor_sum_normSq_tensor_three
import Theorems.Thm_ShiTensor_runLayered_embed_three_blocks
import Theorems.Thm_ShiTensor_accept_weight_or_form_eq_count_form_three_copies
import Theorems.Thm_ShiTensor_tensor_majority_three_accept_weight_closed_form

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem exists_amplified_witness_maj3_ge_of_single_copy_bound (T : QMAFamily → QMAFamily)
    (hwit : ∀ F n, (T F).wit n = 3 * F.wit n)
    (hanc : ∀ F n, (T F).anc n = 2 * n + 3 * F.anc n + 3)
    (hout : ∀ F n, ((T F).out n).val = 3 * n + 3 * F.wit n + 3 * F.anc n + 3)
    (hstruct : ∀ (F : QMAFamily) (n : ℕ),
        ∃ (σ : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)
              → Fin (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))))
          (g2 g3 : Fin (n + n) → Fin (n + ((T F).wit n + ((T F).anc n + 1))))
          (p q : Fin n → Fin ((T F).anc n + 1))
          (e1 e2 e3 : Fin (n + (F.wit n + (F.anc n + 1))) → Fin (n + ((T F).wit n + ((T F).anc n + 1))))
          (rd fan2 fan3 : Layered (n + ((T F).wit n + ((T F).anc n + 1))))
          (u2 u3 : Bits (n + ((T F).wit n + ((T F).anc n + 1))) → Bits (n + ((T F).wit n + ((T F).anc n + 1))))
          (hg2 : Function.Injective g2) (hg3 : Function.Injective g3)
          (he1 : Function.Injective e1) (he2 : Function.Injective e2)
          (he3 : Function.Injective e3),
          σ = Classical.choose (exists_layout_bijection n (F.wit n) (F.anc n))
          ∧ fan2 = Classical.choose (exists_fanout_embedded_pullback n
              (n + ((T F).wit n + ((T F).anc n + 1))) g2 hg2)
          ∧ fan3 = Classical.choose (exists_fanout_embedded_pullback n
              (n + ((T F).wit n + ((T F).anc n + 1))) g3 hg3)
          ∧ (T F).circ n
              = fan2 ++ fan3
                ++ ShiEmbed.embedCirc e1 he1 (F.circ n)
                ++ ShiEmbed.embedCirc e2 he2 (F.circ n)
                ++ ShiEmbed.embedCirc e3 he3 (F.circ n) ++ rd
          ∧ (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
              u.val = v.val → (e1 v).val = (σ u).val)
          ∧ (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
              u.val = n + (F.wit n + (F.anc n + 1)) + v.val → (e2 v).val = (σ u).val)
          ∧ (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
              u.val = 2 * (n + (F.wit n + (F.anc n + 1))) + v.val →
              (e3 v).val = (σ u).val)
          ∧ (∀ (v : Fin (n + n)) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
              u.val
                = (if v.val < n then v.val
                    else n + (F.wit n + (F.anc n + 1)) + (v.val - n)) →
              (g2 v).val = (σ u).val)
          ∧ (∀ (v : Fin (n + n)) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
              u.val
                = (if v.val < n then v.val
                    else 2 * (n + (F.wit n + (F.anc n + 1))) + (v.val - n)) →
              (g3 v).val = (σ u).val)
          ∧ (∀ j : Fin n, (p j).val = F.anc n + 1 + j.val)
          ∧ (∀ j : Fin n, (q j).val = n + 2 * F.anc n + 2 + j.val)
          ∧ (∀ j j' : Fin n, p j ≠ q j')
          ∧ (∀ Φ : QState (n + ((T F).wit n + ((T F).anc n + 1))), runLayered fan2 Φ = fun Y => Φ (u2 Y))
          ∧ (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (j : Fin n),
              u2 Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (p j)))
                = xor (Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (p j))))
                    (Y (Fin.castAdd ((T F).wit n + ((T F).anc n + 1)) j)))
          ∧ (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (k : Fin (n + ((T F).wit n + ((T F).anc n + 1)))),
              (∀ j : Fin n, Fin.natAdd n (Fin.natAdd ((T F).wit n) (p j)) ≠ k) →
                u2 Y k = Y k)
          ∧ (∀ Φ : QState (n + ((T F).wit n + ((T F).anc n + 1))), runLayered fan3 Φ = fun Y => Φ (u3 Y))
          ∧ (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (j : Fin n),
              u3 Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (q j)))
                = xor (Y (Fin.natAdd n (Fin.natAdd ((T F).wit n) (q j))))
                    (Y (Fin.castAdd ((T F).wit n + ((T F).anc n + 1)) j)))
          ∧ (∀ (Y : Bits (n + ((T F).wit n + ((T F).anc n + 1)))) (k : Fin (n + ((T F).wit n + ((T F).anc n + 1)))),
              (∀ j : Fin n, Fin.natAdd n (Fin.natAdd ((T F).wit n) (q j)) ≠ k) →
                u3 Y k = Y k)
          ∧ (∀ ψ : QState (n + ((T F).wit n + ((T F).anc n + 1))),
              runLayered rd ψ
                = fun x => ψ (Function.update x ((T F).out n)
                    (xor (x ((T F).out n))
                      (xor (xor (x (e1 (F.out n)) && x (e2 (F.out n)))
                              (x (e2 (F.out n)) && x (e3 (F.out n))))
                        (x (e1 (F.out n)) && x (e3 (F.out n)))))))
          ∧ (∀ l ∈ rd, LayerOk l)
          ∧ depth rd = 111)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ (F : QMAFamily) (w : PvsNP.Str),
      (∃ ψ, Normalized ψ ∧ c ≤ F.acceptWith (ShiBQP.toBits w) ψ)
      → (∃ Ψ, Normalized Ψ ∧
            3 * c ^ 2 - 2 * c ^ 3 ≤ (T F).acceptWith (ShiBQP.toBits w) Ψ) := by
  sorry

end ShiClassQMA
