import «AMPUNI-boolean-output-final»
import «AMPUNI-run-stack-growth»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMBooleanCleanup
open ShiTMLayoutMachine (Cell Sig)
open ShiTMBooleanIO

/-- There are twenty Cell work stacks and one Boolean input stack to drain. -/
theorem todo_length : todo.length = 21 := by
  simp [todo, Finset.card_erase_of_mem, K, ShiTMRetainedTop.TopK, ShiTMOuterLift.OuterK]

theorem suffixCost_le_size (S : ∀ j, List (Gam j)) :
    suffixCost todo S ≤ ShiTMStackGrowth.size S+21 := by
  rw [suffixCost, todo_length]
  have h : (todo.map (fun k => (S k).length)).sum ≤ ShiTMStackGrowth.size S := by
    rw [todo, Finset.sum_map_toList]
    exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  omega

end ShiTMBooleanCleanup

namespace ShiTMBooleanFinal
open ShiTMLayoutMachine (Cell Sig bit)
open ShiTMBooleanIO

/-- Finalization costs at most twice the total stored data plus a fixed
constant. A bounded source run therefore also bounds final cleanup time. -/
theorem final_output_size_bound (xs : List Bool) (v : Sig) (S : ∀ j, List (Gam j))
    (ha : S accumulator = (xs.map bit).reverse) (ho : S output = []) :
    ∃ steps : Nat,
      steps ≤ 2*ShiTMStackGrowth.size S+24 ∧
      run^[steps] (some ⟨some (.inl .writeOutput), v, S⟩) =
        some (Turing.haltList finiteMachine xs) := by
  obtain ⟨steps, hbound, hr⟩ := final_output_run xs v S ha ho
  have hc := ShiTMBooleanCleanup.suffixCost_le_size S
  have hx : xs.length ≤ ShiTMStackGrowth.size S := by
    have h : (S accumulator).length ≤ ∑ k, (S k).length :=
      Finset.single_le_sum (f := fun k : K => (S k).length)
        (fun k _ => Nat.zero_le _) (Finset.mem_univ accumulator)
    simpa [ha, ShiTMStackGrowth.size] using h
  exact ⟨steps, by omega, hr⟩

end ShiTMBooleanFinal
