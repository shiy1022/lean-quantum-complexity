import «AMPUNI-global-fanout-prefix»

set_option autoImplicit false
namespace ShiTMGlobalFanoutPrefix
open ShiTMRetainedTop

/-- Including global-depth scanning, the prefix remains quadratic in an
input-length bound controlling both numeric headers and source depth. -/
theorem prefix_cost_le (n w a d L : Nat) (S : ∀ j, List (TopGam j))
    (hfields : n+w+a+1 ≤ L) (hdepth : d ≤ L) :
    d+2+ShiTMFanoutStage.stageCost n w a S ≤
      ShiTMFanoutStage.workSize S+82*L*L := by
  have hstage := ShiTMFanoutStage.stageCost_le n w a L S hfields
  have hL : 1 ≤ L := by omega
  have hsquare : L ≤ L*L := by simpa using Nat.mul_le_mul_left L hL
  have hone : 1 ≤ L*L := le_trans hL hsquare
  nlinarith

end ShiTMGlobalFanoutPrefix
