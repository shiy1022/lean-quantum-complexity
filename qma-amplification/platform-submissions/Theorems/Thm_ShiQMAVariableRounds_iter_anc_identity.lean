import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem ShiQMAVariableRounds.iter_anc_identity (F : QMAFamily) (r n : Nat) :
    2 * (iter F r).anc n + (2 * n + 3) =
      3 ^ r * (2 * F.anc n + 2 * n + 3) := by sorry
