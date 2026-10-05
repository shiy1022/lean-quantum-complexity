-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.exists_layout_bijection`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_exists_layout_bijection`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem exists_layout_bijection (n wit anc : ℕ) :
    ∃ σ : Fin (3 * (n + (wit + (anc + 1))) + 1)
        → Fin (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1))),
      Function.Bijective σ
      -- copy 1 input  ↦ role input block, offset 0
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = j → (σ v).val = j)
      -- copy 1 witness ↦ role witness block, offset 0 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = n + j → (σ v).val = n + j)
      -- copy 1 ancilla ↦ role ancilla block, offset 0
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = n + wit + j → (σ v).val = n + 3 * wit + j)
      -- copy 1 output  ↦ role ancilla block, offset anc
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = n + wit + anc → (σ v).val = n + 3 * wit + anc)
      -- copy 2 input   ↦ role ancilla block, offset anc + 1
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = (n + (wit + (anc + 1))) + j →
          (σ v).val = n + 3 * wit + anc + 1 + j)
      -- copy 2 witness ↦ role witness block, offset 1 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = (n + (wit + (anc + 1))) + n + j → (σ v).val = n + wit + j)
      -- copy 2 ancilla ↦ role ancilla block, offset n + anc + 1
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = (n + (wit + (anc + 1))) + n + wit + j →
          (σ v).val = 2 * n + 3 * wit + anc + 1 + j)
      -- copy 2 output  ↦ role ancilla block, offset n + 2 * anc + 1
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = (n + (wit + (anc + 1))) + n + wit + anc →
          (σ v).val = 2 * n + 3 * wit + 2 * anc + 1)
      -- copy 3 input   ↦ role ancilla block, offset n + 2 * anc + 2
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = 2 * (n + (wit + (anc + 1))) + j →
          (σ v).val = 2 * n + 3 * wit + 2 * anc + 2 + j)
      -- copy 3 witness ↦ role witness block, offset 2 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = 2 * (n + (wit + (anc + 1))) + n + j → (σ v).val = n + 2 * wit + j)
      -- copy 3 ancilla ↦ role ancilla block, offset 2 * n + 2 * anc + 2
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = 2 * (n + (wit + (anc + 1))) + n + wit + j →
          (σ v).val = 3 * n + 3 * wit + 2 * anc + 2 + j)
      -- copy 3 output  ↦ role ancilla block, offset 2 * n + 3 * anc + 2
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = 2 * (n + (wit + (anc + 1))) + n + wit + anc →
          (σ v).val = 3 * n + 3 * wit + 3 * anc + 2)
      -- scratch wire   ↦ role output wire
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = 3 * (n + (wit + (anc + 1))) →
          (σ v).val = 3 * n + 3 * wit + 3 * anc + 3) := by
  sorry

end ShiShallow
