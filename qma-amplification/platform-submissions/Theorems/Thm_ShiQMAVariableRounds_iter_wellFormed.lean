import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem ShiQMAVariableRounds.iter_wellFormed (F : QMAFamily) (r : Nat)
    (hF : ShiBQP.WellFormed F.toFamily) :
    ShiBQP.WellFormed (iter F r).toFamily := by sorry
