-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.exists_amplifier_three_block_embedding`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_exists_amplifier_three_block_embedding`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiSpread_Core
import Theorems.Thm_ShiShallow_exists_layout_bijection

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem exists_amplifier_three_block_embedding (T : QMAFamily → QMAFamily)
    (hwit : ∀ (F : QMAFamily) (n : ℕ), (T F).wit n = 3 * F.wit n)
    (hanc : ∀ (F : QMAFamily) (n : ℕ), (T F).anc n = 2 * n + 3 * F.anc n + 3)
    (hout : ∀ (F : QMAFamily) (n : ℕ),
        ((T F).out n).val = 3 * n + 3 * F.wit n + 3 * F.anc n + 3) :
    ∀ (F : QMAFamily) (n : ℕ)
      (σ : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1) → Fin (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))))
      (p q : Fin n → Fin ((T F).anc n + 1))
      (e1 e2 e3 : Fin (n + (F.wit n + (F.anc n + 1))) → Fin (n + ((T F).wit n + ((T F).anc n + 1)))),
      σ = Classical.choose (exists_layout_bijection n (F.wit n) (F.anc n)) →
      (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
          u.val = v.val → (e1 v).val = (σ u).val) →
      (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
          u.val = n + (F.wit n + (F.anc n + 1)) + v.val → (e2 v).val = (σ u).val) →
      (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)),
          u.val = 2 * (n + (F.wit n + (F.anc n + 1))) + v.val → (e3 v).val = (σ u).val) →
      (∀ j : Fin n, (p j).val = F.anc n + 1 + j.val) →
      (∀ j : Fin n, (q j).val = n + 2 * F.anc n + 2 + j.val) →
      ∃ e : Fin (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1))) + (n + (F.wit n + (F.anc n + 1)))) → Fin (n + ((T F).wit n + ((T F).anc n + 1))),
        Function.Injective e
        ∧ (∀ v : Fin (n + (F.wit n + (F.anc n + 1))),
            e (Fin.castAdd (n + (F.wit n + (F.anc n + 1))) (Fin.castAdd (n + (F.wit n + (F.anc n + 1))) v)) = e1 v)
        ∧ (∀ v : Fin (n + (F.wit n + (F.anc n + 1))),
            e (Fin.castAdd (n + (F.wit n + (F.anc n + 1))) (Fin.natAdd (n + (F.wit n + (F.anc n + 1))) v)) = e2 v)
        ∧ (∀ v : Fin (n + (F.wit n + (F.anc n + 1))),
            e (Fin.natAdd (n + (F.wit n + (F.anc n + 1)) + (n + (F.wit n + (F.anc n + 1)))) v) = e3 v)
        ∧ (∀ k : Fin (n + ((T F).wit n + ((T F).anc n + 1))), ShiSpread.OffImage e k ↔ k = (T F).out n)
        ∧ (∀ i : Fin n, e1 (Fin.castAdd (F.wit n + (F.anc n + 1)) i)
            = Fin.castAdd ((T F).wit n + ((T F).anc n + 1)) i)
        ∧ (∀ j : Fin n, e2 (Fin.castAdd (F.wit n + (F.anc n + 1)) j)
            = Fin.natAdd n (Fin.natAdd ((T F).wit n) (p j)))
        ∧ (∀ j : Fin n, e3 (Fin.castAdd (F.wit n + (F.anc n + 1)) j)
            = Fin.natAdd n (Fin.natAdd ((T F).wit n) (q j)))
        ∧ (∀ (j : Fin (F.wit n)) (j' : Fin ((T F).wit n)), j'.val = j.val →
            e1 (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j))
              = Fin.natAdd n (Fin.castAdd ((T F).anc n + 1) j'))
        ∧ (∀ (j : Fin (F.wit n)) (j' : Fin ((T F).wit n)), j'.val = F.wit n + j.val →
            e2 (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j))
              = Fin.natAdd n (Fin.castAdd ((T F).anc n + 1) j'))
        ∧ (∀ (j : Fin (F.wit n)) (j' : Fin ((T F).wit n)), j'.val = 2 * F.wit n + j.val →
            e3 (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j))
              = Fin.natAdd n (Fin.castAdd ((T F).anc n + 1) j'))
        ∧ (∀ (l : Fin (F.anc n + 1)) (l' : Fin ((T F).anc n + 1)), l'.val = l.val →
            e1 (Fin.natAdd n (Fin.natAdd (F.wit n) l))
              = Fin.natAdd n (Fin.natAdd ((T F).wit n) l'))
        ∧ (∀ (l : Fin (F.anc n + 1)) (l' : Fin ((T F).anc n + 1)),
            l'.val = n + F.anc n + 1 + l.val →
            e2 (Fin.natAdd n (Fin.natAdd (F.wit n) l))
              = Fin.natAdd n (Fin.natAdd ((T F).wit n) l'))
        ∧ (∀ (l : Fin (F.anc n + 1)) (l' : Fin ((T F).anc n + 1)),
            l'.val = 2 * n + 2 * F.anc n + 2 + l.val →
            e3 (Fin.natAdd n (Fin.natAdd (F.wit n) l))
              = Fin.natAdd n (Fin.natAdd ((T F).wit n) l')) := by
  sorry

end ShiClassQMA
