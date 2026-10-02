import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem solution (F : QMAFamily) (r : Nat)
    (hF : ShiBQP.WellFormed F.toFamily) :
    ShiBQP.WellFormed (iter F r).toFamily := by
  induction r with
  | zero => exact hF
  | succ r ih =>
      exact ampFamilyX_resource_identities_and_regularity.2.2.2.2.1 (iter F r) ih
