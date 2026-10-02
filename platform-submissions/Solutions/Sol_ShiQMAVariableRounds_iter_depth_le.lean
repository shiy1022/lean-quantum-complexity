import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity
import Theorems.Thm_ShiQMAVariableRounds_iter_depth_identity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem solution (F : QMAFamily) (r n : Nat) :
    depth ((iter F r).circ n) ≤ 3 ^ r * (depth (F.circ n) + 113) := by
  have h := iter_depth_identity F r n
  nlinarith
