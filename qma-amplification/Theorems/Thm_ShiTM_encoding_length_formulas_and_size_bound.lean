-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.encoding_length_formulas_and_size_bound`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_encoding_length_formulas_and_size_bound`. The real proof is on prove2.me.
import Definitions.Def_ShiBQP_Core
import Theorems.Thm_ShiShallow_gateCount_le_depth_mul_width_of_layerOk_core

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2 Turing.TM2.Stmt

theorem encoding_length_formulas_and_size_bound :
    (∀ k : ℕ, (ShiBQP.encNat k).length = k + 1) ∧
    (∀ ls : List PvsNP.Str,
      (ShiBQP.encStr ls).length = ls.length + 1 + (ls.map List.length).sum) ∧
    (∀ (m : ℕ) (i : Fin m),
      (ShiBQP.encInstr (ShiShallow.Instr.h i)).length = (i : ℕ) + 2) ∧
    (∀ (m : ℕ) (i : Fin m),
      (ShiBQP.encInstr (ShiShallow.Instr.s i)).length = (i : ℕ) + 3) ∧
    (∀ (m : ℕ) (i : Fin m),
      (ShiBQP.encInstr (ShiShallow.Instr.t i)).length = (i : ℕ) + 4) ∧
    (∀ (m : ℕ) (i : Fin m),
      (ShiBQP.encInstr (ShiShallow.Instr.x i)).length = (i : ℕ) + 5) ∧
    (∀ (m : ℕ) (i j : Fin m) (hij : i ≠ j),
      (ShiBQP.encInstr (ShiShallow.Instr.cnot i j hij)).length
        = (i : ℕ) + (j : ℕ) + 7) ∧
    (∀ (m : ℕ) (g : ShiShallow.Instr m), (ShiBQP.encInstr g).length ≤ 2 * m + 5) ∧
    (∀ (m : ℕ) (l : List (ShiShallow.Instr m)),
      (ShiBQP.encLayer l).length
        = l.length + 1 + (l.map (fun g => (ShiBQP.encInstr g).length)).sum) ∧
    (∀ (m : ℕ) (c : ShiShallow.Layered m),
      (ShiBQP.encCirc c).length
        = c.length + 1 + (c.map (fun l => (ShiBQP.encLayer l).length)).sum) ∧
    (∀ (F : ShiClass.Family) (n : ℕ),
      (ShiBQP.encFamilyAt F n).length
        = F.anc n + ((F.out n : ℕ)) + 2 + (ShiBQP.encCirc (F.circ n)).length) ∧
    (∀ (m : ℕ) (c : ShiShallow.Layered m),
      (ShiBQP.encCirc c).length
        ≤ 2 * ShiShallow.depth c + 1 + (c.map List.length).sum * (2 * m + 6)) ∧
    (∀ (m : ℕ) (c : ShiShallow.Layered m), (∀ l ∈ c, ShiShallow.LayerOk l) →
      (ShiBQP.encCirc c).length
        ≤ 2 * ShiShallow.depth c + 1 + ShiShallow.depth c * m * (2 * m + 6)) := by
  sorry

end ShiTM
