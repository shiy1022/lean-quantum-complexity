import ReversibleInitializationAddressBudget
import ReversibleResourcePrelude

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def resourceCounterPolynomials (tm : Turing.FinTM2) (time : Polynomial Nat) :
    WorkspaceRegister → Polynomial Nat :=
  operationResultPolynomial (workspaceOperations tm)
    (operationResultPolynomial (resourceLayoutOperations tm)
      (fun r => if r = 0 then Polynomial.X else if r = 1 then time else 0))

/-- Every counter returned by the actual resource prelude is a polynomial evaluation. -/
theorem resourceCounterPolynomials_eval (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat) :
    (fun r => (resourceCounterPolynomials tm time r).eval n) =
      operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) := by
  simp only [resourceCounterPolynomials, operationResultPolynomial_eval]
  rw [show (fun r : WorkspaceRegister =>
      (if r = 0 then Polynomial.X else if r = 1 then time else 0).eval n) = resourceBudgetState n (time.eval n) by
    funext r
    by_cases h0 : r = 0 <;> by_cases h1 : r = 1 <;> simp [h0, h1, resourceBudgetState]]
  rw [resourceLayout_result]

noncomputable def resourceCounterBudgetPolynomial (tm : Turing.FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  Finset.univ.sum (resourceCounterPolynomials tm time)

theorem resourceCounterBudgetPolynomial_bound (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (r : WorkspaceRegister) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r ≤
      (resourceCounterBudgetPolynomial tm time).eval n := by
  rw [← congrFun (resourceCounterPolynomials_eval tm time n) r]
  have hs : (resourceCounterBudgetPolynomial tm time).eval n =
      Finset.univ.sum (fun j => (resourceCounterPolynomials tm time j).eval n) := by
    exact Polynomial.eval_finsetSum _ _ _
  rw [hs]
  exact Finset.single_le_sum (f := fun j : WorkspaceRegister => (resourceCounterPolynomials tm time j).eval n)
    (fun j hj => Nat.zero_le _) (Finset.mem_univ r)

theorem resourceResult_raw (tm : Turing.FinTM2) (n time : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n time) 0 = n := by
  simp [workspaceOperations, workspaceInitial, operationResult, GeneratorOperation.apply, AffineAtom.apply]

theorem resourceResult_capacity (tm : Turing.FinTM2) (n time : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n time) 2 = n + time * machinePushBound tm + 1 := by
  simp [workspaceOperations, workspaceInitial, operationResult, GeneratorOperation.apply, AffineAtom.apply]

end ShiReversibleGenerator
