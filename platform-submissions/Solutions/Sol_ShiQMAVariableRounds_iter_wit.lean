import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem solution (F : QMAFamily) (r n : Nat) :
    (iter F r).wit n = 3 ^ r * F.wit n := by
  induction r with
  | zero => simp [iter]
  | succ r ih =>
      rw [iter, ampFamilyX_resource_identities_and_regularity.1, ih, pow_succ]
      ring
