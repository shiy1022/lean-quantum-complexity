import «AMPUNI-boolean-controller-valid-run»
import «AMPUNI-boolean-cleanup-bounds»
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMBooleanWrapper
open ShiTMLayoutMachine (Cell Sig bit)
open ShiTMRetainedTop
open ShiTMBooleanIO (K Gam input output source scratch accumulator)
variable {L : Type} [DecidableEq L] [Fintype L]

theorem initialTop_size (xs : List Bool) : ShiTMStackGrowth.size (initialTop xs) = xs.length := by
  have h : (fun k => (initialTop xs k).length) =
      (fun k => if k = cellSource then xs.length else 0) := by
    funext k
    by_cases hk : k = cellSource
    · subst k; simp [initialTop]
    · simp [initialTop, hk]
  unfold ShiTMStackGrowth.size
  rw [h]
  simp

theorem extend_empty_size (S : ∀ k, List (TopGam k)) :
    ShiTMStackGrowth.size (ShiTMIOFrame.extendStacks S (fun _ => [])) =
      ShiTMStackGrowth.size S := by
  simp [ShiTMStackGrowth.size, Fintype.sum_sum_type, ShiTMIOFrame.extendStacks]

/-- Boolean loading, output conversion, and canonical cleanup preserve a
polynomial bound for any typed body with bounded per-step stack growth.
Totality on malformed inputs is still a separate obligation. -/
theorem valid_input_outputs_bound (M : L → Stmt TopGam L Sig) (main terminal : L)
    (hterminal : M terminal = .halt) (C : Nat)
    (hgrowth : ∀ l v S, ShiTMStackGrowth.size (stepAux (M l) v S).stk ≤ ShiTMStackGrowth.size S+C)
    (xs ys : List Bool) (bodySteps : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hr : (ShiTMSubroutine.run M)^[bodySteps]
      (some ⟨some main, none, initialTop xs⟩) = some ⟨some terminal, v, S⟩)
    (ho : S cellOutput = (ys.map bit).reverse) :
    Nonempty (Turing.TM2OutputsInTime (finiteMachine M main terminal) xs (some ys)
      ((2*C+1)*bodySteps+4*xs.length+28)) := by
  obtain ⟨steps, hb, hrun⟩ := valid_input_run M main terminal hterminal xs ys bodySteps v S hr ho
  have hs : ShiTMStackGrowth.size S ≤ xs.length+bodySteps*C := by
    have h := ShiTMStackGrowth.run_size_le M C hgrowth bodySteps
      ⟨some main, none, initialTop xs⟩ ⟨some terminal, v, S⟩ hr
    simpa only [initialTop_size] using h
  have hc := ShiTMBooleanCleanup.suffixCost_le_size
    (ShiTMIOFrame.extendStacks S (fun _ => []))
  rw [extend_empty_size] at hc
  have hy : ys.length ≤ ShiTMStackGrowth.size S := by
    have h : (S cellOutput).length ≤ ∑ k, (S k).length :=
      Finset.single_le_sum (f := fun k : TopK => (S k).length)
        (fun k _ => Nat.zero_le _) (Finset.mem_univ cellOutput)
    simpa [ho, ShiTMStackGrowth.size] using h
  refine ⟨⟨⟨steps, hrun⟩, ?_⟩⟩
  nlinarith

end ShiTMBooleanWrapper
