-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.encInstr_of_embedInstr_tag_preserved_index_remapped`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_encInstr_of_embedInstr_tag_preserved_index_remapped`. The real proof is on prove2.me.
import Definitions.Def_ShiBQP_Core
import Definitions.Def_ShiEmbed_Core
import Theorems.Thm_ShiTM_encoding_length_formulas_and_size_bound

set_option autoImplicit false

namespace ShiTM

theorem encInstr_of_embedInstr_tag_preserved_index_remapped :
    (∀ (m n : ℕ) (e : Fin m → Fin n) (he : Function.Injective e),
      -- 1. per instruction: tag preserved, index remapped
      (∀ i : Fin m, ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.h i))
          = ShiBQP.encNat 0 ++ ShiBQP.encNat ((e i : ℕ))) ∧
      (∀ i : Fin m, ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.s i))
          = ShiBQP.encNat 1 ++ ShiBQP.encNat ((e i : ℕ))) ∧
      (∀ i : Fin m, ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.t i))
          = ShiBQP.encNat 2 ++ ShiBQP.encNat ((e i : ℕ))) ∧
      (∀ i : Fin m, ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.x i))
          = ShiBQP.encNat 3 ++ ShiBQP.encNat ((e i : ℕ))) ∧
      (∀ (i j : Fin m) (hij : i ≠ j),
        ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.cnot i j hij))
          = ShiBQP.encNat 4 ++ ShiBQP.encNat ((e i : ℕ)) ++ ShiBQP.encNat ((e j : ℕ))) ∧
      -- 2a. the flattening commutes with the remap
      (∀ l : List (ShiShallow.Instr m),
        (ShiEmbed.embedLayer e he l).map ShiBQP.encInstr
          = l.map (fun g => ShiBQP.encInstr (ShiEmbed.embedInstr e he g))) ∧
      (∀ c : ShiShallow.Layered m,
        (ShiEmbed.embedCirc e he c).map ShiBQP.encLayer
          = c.map (fun l => ShiBQP.encLayer (ShiEmbed.embedLayer e he l))) ∧
      -- 2b. the length prefixes are the ORIGINAL counts, copied verbatim
      (∀ l : List (ShiShallow.Instr m),
        ShiBQP.encLayer (ShiEmbed.embedLayer e he l)
          = ShiBQP.encNat l.length
              ++ (l.map (fun g => ShiBQP.encInstr (ShiEmbed.embedInstr e he g))).flatten) ∧
      (∀ c : ShiShallow.Layered m,
        ShiBQP.encCirc (ShiEmbed.embedCirc e he c)
          = ShiBQP.encNat c.length
              ++ (c.map (fun l => ShiBQP.encLayer (ShiEmbed.embedLayer e he l))).flatten) ∧
      -- 2c. layer counts and instruction counts are unchanged
      (∀ l : List (ShiShallow.Instr m), (ShiEmbed.embedLayer e he l).length = l.length) ∧
      (∀ c : ShiShallow.Layered m, (ShiEmbed.embedCirc e he c).length = c.length) ∧
      (∀ c : ShiShallow.Layered m,
        ShiShallow.depth (ShiEmbed.embedCirc e he c) = ShiShallow.depth c) ∧
      (∀ c : ShiShallow.Layered m,
        (ShiEmbed.embedCirc e he c).map List.length = c.map List.length) ∧
      (∀ c : ShiShallow.Layered m, ∀ l ∈ c,
        (ShiEmbed.embedLayer e he l).length = l.length) ∧
      -- 3. the length identity, at the remapped indices (SIZE-1)
      (∀ i : Fin m,
        (ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.h i))).length
          = (e i : ℕ) + 2) ∧
      (∀ i : Fin m,
        (ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.s i))).length
          = (e i : ℕ) + 3) ∧
      (∀ i : Fin m,
        (ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.t i))).length
          = (e i : ℕ) + 4) ∧
      (∀ i : Fin m,
        (ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.x i))).length
          = (e i : ℕ) + 5) ∧
      (∀ (i j : Fin m) (hij : i ≠ j),
        (ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.cnot i j hij))).length
          = (e i : ℕ) + (e j : ℕ) + 7)) ∧
    -- NON-VACUITY: a concrete shift `Fin 2 → Fin 5`, at literal bit lists
    (∃ (e : Fin 2 → Fin 5) (he : Function.Injective e),
      (e ⟨0, by omega⟩ : ℕ) = 2 ∧ (e ⟨1, by omega⟩ : ℕ) = 3 ∧
      ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.h ⟨0, by omega⟩))
          = [false, true, true, false] ∧
      ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.s ⟨1, by omega⟩))
          = [true, false, true, true, true, false] ∧
      ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.t ⟨0, by omega⟩))
          = [true, true, false, true, true, false] ∧
      ShiBQP.encInstr (ShiEmbed.embedInstr e he (ShiShallow.Instr.x ⟨1, by omega⟩))
          = [true, true, true, false, true, true, true, false] ∧
      ShiBQP.encInstr (ShiEmbed.embedInstr e he
          (ShiShallow.Instr.cnot ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide)))
          = [true, true, true, true, false, true, true, false, true, true, true, false] ∧
      ShiBQP.encLayer (ShiEmbed.embedLayer e he
          [ShiShallow.Instr.h ⟨0, by omega⟩, ShiShallow.Instr.x ⟨1, by omega⟩])
          = ShiBQP.encNat 2 ++ [false, true, true, false]
              ++ [true, true, true, false, true, true, true, false]) := by
  sorry

end ShiTM
