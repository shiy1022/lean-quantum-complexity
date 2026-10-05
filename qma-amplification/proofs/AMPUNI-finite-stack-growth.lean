import «AMPUNI-run-stack-growth»
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMStackGrowth
variable {K L V : Type} [DecidableEq K] [Fintype K] {G : K → Type}

/-- A syntactic bound on the number of pushes in one machine statement. -/
def pushBudget : Stmt G L V → Nat
  | .push _ _ q => pushBudget q + 1
  | .peek _ _ q => pushBudget q
  | .pop _ _ q => pushBudget q
  | .load _ q => pushBudget q
  | .branch _ q r => max (pushBudget q) (pushBudget r)
  | .goto _ => 0
  | .halt => 0

theorem size_push_le (S : ∀ k, List (G k)) (j : K) (a : G j) :
    size (Function.update S j (a :: S j)) ≤ size S + 1 := by
  have h : ∀ k, (Function.update S j (a :: S j) k).length ≤
      (S k).length + if k = j then 1 else 0 := by
    intro k
    by_cases hk : k = j
    · subst k; simp
    · simp [Function.update_of_ne hk, hk]
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) => h k)
  simpa [size, Finset.sum_add_distrib] using hs

theorem size_pop_le (S : ∀ k, List (G k)) (j : K) :
    size (Function.update S j (S j).tail) ≤ size S := by
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k = j
  · subst k; simp
  · simp [Function.update_of_ne hk]

theorem stepAux_size_le (q : Stmt G L V) (v : V) (S : ∀ k, List (G k)) :
    size (stepAux q v S).stk ≤ size S + pushBudget q := by
  induction q generalizing v S with
  | push j f q ih =>
      have h := ih v (Function.update S j (f v :: S j))
      have hs := size_push_le S j (f v)
      change size (stepAux q v (Function.update S j (f v :: S j))).stk ≤ _
      simp only [pushBudget]
      omega
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
      have h := ih (f v (S j).head?) (Function.update S j (S j).tail)
      have hs := size_pop_le S j
      change size (stepAux q (f v (S j).head?) (Function.update S j (S j).tail)).stk ≤ _
      simp only [pushBudget]
      omega
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
      simp only [stepAux, pushBudget]
      cases hf : f v <;> simp only [Bool.false_eq_true, ↓reduceIte, cond_false, cond_true]
      · exact le_trans (ihr v S) (Nat.add_le_add_left (le_max_right _ _) _)
      · exact le_trans (ihq v S) (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp [stepAux, pushBudget]
  | halt => simp [stepAux, pushBudget]

/-- Every finite-label machine has a uniform stack-growth constant, with no
semantic assumptions about its input or its execution. -/
theorem finite_growth [Fintype L] (M : L → Stmt G L V) :
    ∃ C : Nat, ∀ l v S, size (stepAux (M l) v S).stk ≤ size S + C := by
  refine ⟨∑ l, pushBudget (M l), ?_⟩
  intro l v S
  apply le_trans (stepAux_size_le (M l) v S)
  apply Nat.add_le_add_left
  exact Finset.single_le_sum (f := fun l => pushBudget (M l))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

end ShiTMStackGrowth
