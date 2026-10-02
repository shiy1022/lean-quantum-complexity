import Definitions.Def_ShiQMAVariableRoundsPolynomialFamily
import Theorems.Thm_ShiQMAVariableRounds_copies_roundsFor_le_all
import Theorems.Thm_ShiQMAVariableRounds_iter_depth_le
import Theorems.Thm_ShiQMAVariableRounds_iter_wit_add_anc_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiShallow ShiClassQMA ShiQMAErrorIteration Polynomial ShiQMAVariableRounds

theorem ShiQMAVariableRounds.polynomialFamily_polyBounded (F : QMAFamily) (p : Polynomial ℕ)
    (hF : ShiBQP.PolyBounded F.toFamily) :
    ShiBQP.PolyBounded (polynomialFamily F p).toFamily := by sorry
