import Definitions.Def_ShiQMAVariableRounds
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiClassQMAAmpX ShiQMAVariableRounds

theorem solution (F : QMAFamily) (r n : Nat) :
    2 * depth ((iter F r).circ n) + 113 =
      3 ^ r * (2 * depth (F.circ n) + 113) := by
  induction r with
  | zero => simp [iter]
  | succ r ih =>
      rw [iter, ampFamilyX_resource_identities_and_regularity.2.2.2.1, pow_succ]
      calc
        2 * (3 * depth ((iter F r).circ n) + 113) + 113 =
            3 * (2 * depth ((iter F r).circ n) + 113) := by omega
        _ = 3 * (3 ^ r * (2 * depth (F.circ n) + 113)) := by rw [ih]
        _ = 3 ^ r * 3 * (2 * depth (F.circ n) + 113) := by ring
