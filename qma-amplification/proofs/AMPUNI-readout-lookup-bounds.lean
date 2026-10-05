import «AMPUNI-layout-data»

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ShiTMReadoutLookup
open ShiTMLayoutMachine

/-- The numerical cost function is bounded by the sum over table entries,
for every numeric index. Relating this function to an actual machine run
still requires the valid-index hypothesis in `lookup_run`. -/
theorem cost_le_table_sum (ps : List (Nat × Nat)) (out : Nat) :
    cost ps out ≤ (ps.map (fun p => 2*p.1+p.2+3)).sum := by
  induction ps generalizing out with
  | nil => simp [cost]
  | cons p ps ih =>
      rcases p with ⟨width, base⟩
      simp only [cost, List.map_cons, List.sum_cons]
      split
      · omega
      · exact Nat.add_le_add_left (ih (out-width)) _

end ShiTMReadoutLookup
