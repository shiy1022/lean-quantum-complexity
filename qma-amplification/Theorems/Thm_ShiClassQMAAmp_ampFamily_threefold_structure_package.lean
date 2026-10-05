-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMAAmp.ampFamily_threefold_structure_package`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMAAmp_ampFamily_threefold_structure_package`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMAAmp
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiEmbed_Core
import Theorems.Thm_ShiShallow_exists_layout_bijection
import Theorems.Thm_ShiShallow_exists_fanout_embedded_pullback
import Theorems.Thm_ShiShallow_exists_majority_readout_at_wires_layerOk_depth

set_option autoImplicit false

open ShiShallow ShiClassQMA

namespace ShiClassQMAAmp

theorem ampFamily_threefold_structure_package :
    (∀ (F : QMAFamily) (n : ℕ),
      ∃ (σ : Fin (3 * (n + (F.wit n + (F.anc n + 1))) + 1)
            → Fin (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1))))
        (g2 g3 : Fin (n + n)
          → Fin (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
        (p q : Fin n → Fin ((ampFamily F).anc n + 1))
        (e1 e2 e3 : Fin (n + (F.wit n + (F.anc n + 1)))
          → Fin (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
        (rd fan2 fan3 : Layered (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
        (u2 u3 : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1)))
          → Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
        (hg2 : Function.Injective g2) (hg3 : Function.Injective g3)
        (he1 : Function.Injective e1) (he2 : Function.Injective e2)
        (he3 : Function.Injective e3),
        σ = Classical.choose (ShiShallow.exists_layout_bijection n (F.wit n) (F.anc n))
        ∧ fan2 = Classical.choose (ShiShallow.exists_fanout_embedded_pullback n
            (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))) g2 hg2)
        ∧ fan3 = Classical.choose (ShiShallow.exists_fanout_embedded_pullback n
            (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))) g3 hg3)
        ∧ (ampFamily F).circ n
            = fan2 ++ fan3
              ++ ShiEmbed.embedCirc e1 he1 (F.circ n)
              ++ ShiEmbed.embedCirc e2 he2 (F.circ n)
              ++ ShiEmbed.embedCirc e3 he3 (F.circ n) ++ rd
        ∧ (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin _),
            u.val = v.val → (e1 v).val = (σ u).val)
        ∧ (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin _),
            u.val = n + (F.wit n + (F.anc n + 1)) + v.val → (e2 v).val = (σ u).val)
        ∧ (∀ (v : Fin (n + (F.wit n + (F.anc n + 1)))) (u : Fin _),
            u.val = 2 * (n + (F.wit n + (F.anc n + 1))) + v.val →
            (e3 v).val = (σ u).val)
        ∧ (∀ (v : Fin (n + n)) (u : Fin _),
            u.val
              = (if v.val < n then v.val
                  else n + (F.wit n + (F.anc n + 1)) + (v.val - n)) →
            (g2 v).val = (σ u).val)
        ∧ (∀ (v : Fin (n + n)) (u : Fin _),
            u.val
              = (if v.val < n then v.val
                  else 2 * (n + (F.wit n + (F.anc n + 1))) + (v.val - n)) →
            (g3 v).val = (σ u).val)
        ∧ (∀ j : Fin n, (p j).val = F.anc n + 1 + j.val)
        ∧ (∀ j : Fin n, (q j).val = n + 2 * F.anc n + 2 + j.val)
        ∧ (∀ j j' : Fin n, p j ≠ q j')
        ∧ (∀ Φ : QState (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))),
            runLayered fan2 Φ = fun Y => Φ (u2 Y))
        ∧ (∀ (Y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
            (j : Fin n),
            u2 Y (Fin.natAdd n (Fin.natAdd ((ampFamily F).wit n) (p j)))
              = xor (Y (Fin.natAdd n (Fin.natAdd ((ampFamily F).wit n) (p j))))
                  (Y (Fin.castAdd ((ampFamily F).wit n + ((ampFamily F).anc n + 1)) j)))
        ∧ (∀ (Y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
            (k : Fin (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1)))),
            (∀ j : Fin n, Fin.natAdd n (Fin.natAdd ((ampFamily F).wit n) (p j)) ≠ k) →
              u2 Y k = Y k)
        ∧ (∀ Φ : QState (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))),
            runLayered fan3 Φ = fun Y => Φ (u3 Y))
        ∧ (∀ (Y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
            (j : Fin n),
            u3 Y (Fin.natAdd n (Fin.natAdd ((ampFamily F).wit n) (q j)))
              = xor (Y (Fin.natAdd n (Fin.natAdd ((ampFamily F).wit n) (q j))))
                  (Y (Fin.castAdd ((ampFamily F).wit n + ((ampFamily F).anc n + 1)) j)))
        ∧ (∀ (Y : Bits (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))))
            (k : Fin (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1)))),
            (∀ j : Fin n, Fin.natAdd n (Fin.natAdd ((ampFamily F).wit n) (q j)) ≠ k) →
              u3 Y k = Y k)
        ∧ (∀ ψ : QState (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1))),
            runLayered rd ψ
              = fun x => ψ (Function.update x ((ampFamily F).out n)
                  (xor (x ((ampFamily F).out n))
                    (xor (xor (x (e1 (F.out n)) && x (e2 (F.out n)))
                            (x (e2 (F.out n)) && x (e3 (F.out n))))
                      (x (e1 (F.out n)) && x (e3 (F.out n)))))))
        ∧ (∀ l ∈ rd, LayerOk l)
        ∧ depth rd = 111)
    ∧ ((ampFamily
          { anc := fun _ => 0, wit := fun _ => 1, circ := fun _ => [],
            out := fun n => ⟨0, by omega⟩ }).circ 2
          = ampFan2 2 1 0 ++ ampFan3 2 1 0 ++ [] ++ [] ++ []
              ++ ampRead 2 1 0 ⟨0, by omega⟩
        ∧ depth (ampRead 2 1 0 ⟨0, by omega⟩) = 111
        ∧ depth ((ampFamily
            { anc := fun _ => 0, wit := fun _ => 1, circ := fun _ => [],
              out := fun n => ⟨0, by omega⟩ }).circ 2) = 113) := by
  sorry

end ShiClassQMAAmp
