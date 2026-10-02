import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem solution (F : QMAFamily) (r n : Nat) :
    2 * (iter F r).anc n + (2 * n + 3) =
      3 ^ r * (2 * F.anc n + 2 * n + 3) := by
  induction r with
  | zero => simp [iter]; omega
  | succ r ih =>
      rw [iter, ampFamilyX_resource_identities_and_regularity.2.1, pow_succ]
      calc
        2 * (2 * n + 3 * (iter F r).anc n + 3) + (2 * n + 3) =
            3 * (2 * (iter F r).anc n + (2 * n + 3)) := by omega
        _ = 3 * (3 ^ r * (2 * F.anc n + 2 * n + 3)) := by rw [ih]
        _ = 3 ^ r * 3 * (2 * F.anc n + 2 * n + 3) := by ring
