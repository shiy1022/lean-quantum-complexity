import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity
import Theorems.Thm_ShiQMAVariableRounds_iter_wit
import Theorems.Thm_ShiQMAVariableRounds_iter_anc_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem solution (F : QMAFamily) (r n : Nat) :
    (iter F r).wit n + (iter F r).anc n ≤
      3 ^ r * (F.wit n + F.anc n + 2 * n + 3) := by
  have hw := iter_wit F r n
  have ha := iter_anc_le F r n
  nlinarith
