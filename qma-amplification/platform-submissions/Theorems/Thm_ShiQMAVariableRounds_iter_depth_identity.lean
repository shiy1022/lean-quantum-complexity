import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem ShiQMAVariableRounds.iter_depth_identity (F : QMAFamily) (r n : Nat) :
    2 * depth ((iter F r).circ n) + 113 =
      3 ^ r * (2 * depth (F.circ n) + 113) := by sorry
