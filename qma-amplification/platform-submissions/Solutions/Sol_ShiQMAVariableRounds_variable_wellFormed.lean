import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity
import Theorems.Thm_ShiQMAVariableRounds_iter_wellFormed

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem solution (F : QMAFamily) (rounds : Nat → Nat)
    (hF : ShiBQP.WellFormed F.toFamily) :
    ShiBQP.WellFormed (varying F rounds).toFamily := by
  intro n l hl
  exact iter_wellFormed F (rounds n) hF n l hl
