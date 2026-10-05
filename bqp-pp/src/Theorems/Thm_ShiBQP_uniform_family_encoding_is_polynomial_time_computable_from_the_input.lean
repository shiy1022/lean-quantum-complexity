-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_uniform_family_encoding_is_polynomial_time_computable_from_the_input`. The real proof is on prove2.me.
import Definitions.Def_ShiBQP_Core
import Theorems.Thm_PvsNP_polyTimeComputable_comp
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Turing Turing.TM2

namespace ShiBQP

theorem uniform_family_encoding_is_polynomial_time_computable_from_the_input :
    (∀ F : ShiClass.Family, ShiBQP.Uniform F →
        ∃ g : PvsNP.Str → PvsNP.Str, PvsNP.PolyTimeComputable g ∧
          ∀ x : PvsNP.Str, g x = ShiBQP.encFamilyAt F x.length)
      ∧ PvsNP.PolyTimeComputable (fun x : PvsNP.Str => ShiBQP.unary x.length)
      ∧ (∃ F : ShiClass.Family, ∃ g : PvsNP.Str → PvsNP.Str,
          ShiBQP.Uniform F ∧ PvsNP.PolyTimeComputable g ∧
          (∀ x : PvsNP.Str, g x = ShiBQP.encFamilyAt F x.length) ∧
          g [] = [false, false, false] ∧
          g [true, false, true] = [true, true, true, false, false, false] ∧
          ShiBQP.encFamilyAt F 0 = [false, false, false] ∧
          ShiBQP.encFamilyAt F 3 = [true, true, true, false, false, false])
      ∧ ShiBQP.unary ([] : PvsNP.Str).length = []
      ∧ ShiBQP.unary ([true, false, true] : PvsNP.Str).length = [true, true, true] := by
  sorry

end ShiBQP
