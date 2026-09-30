import «AMPUNI-fanout-stage-run»
import «AMPUNI-fanout-cost»
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ShiTMFanoutStage
open ShiTMLayoutMachine ShiTMRetainedTop
open ShiTMFanoutPrepare (port base)

def workSize (S : ∀ j, List (TopGam j)) : Nat :=
  (S (port 0)).length + (S (port 1)).length + (S (port 2)).length

theorem stageCost_eq (n w a : Nat) (S : ∀ j, List (TopGam j)) :
    stageCost n w a S = workSize S + 4*(n+w+a) +
      base false n w a + base true n w a + 4*n + 27 +
      emitCost n (base false n w a) + emitCost n (base true n w a) := by
  simp only [stageCost, blockCost, ShiTMFanoutPrepare.cost,
    ShiTMFanoutPrepare.clearCost, workSize]
  omega

/-- Both fanouts, both preparations, all handoffs, and final cleanup have a
single quadratic bound; old work-register contents contribute only linearly. -/
theorem stageCost_le (n w a L : Nat) (S : ∀ j, List (TopGam j))
    (hlen : n+w+a+1 ≤ L) :
    stageCost n w a S ≤ workSize S + 79*L*L := by
  have hn : n ≤ L := by omega
  have hL : 1 ≤ L := by omega
  have hs : n+w+a ≤ L := by omega
  have hb0 : base false n w a ≤ 3*L := by simp [base]; omega
  have hb1 : base true n w a ≤ 3*L := by simp [base]; omega
  have he0 : emitCost n (base false n w a) ≤ 19*L*L :=
    ShiTMFanout.fanout_cost_le n _ L hn hb0 hL
  have he1 : emitCost n (base true n w a) ≤ 19*L*L :=
    ShiTMFanout.fanout_cost_le n _ L hn hb1 hL
  have hsq : L ≤ L*L := by simpa using Nat.mul_le_mul_left L hL
  have hone : 1 ≤ L*L := le_trans hL hsq
  have hrest : 4*(n+w+a) + base false n w a + base true n w a + 4*n + 27 ≤
      41*L*L := by nlinarith
  rw [stageCost_eq]
  nlinarith

end ShiTMFanoutStage
