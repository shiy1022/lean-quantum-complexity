import «AMPUNI-total-polynomial-clocked-bounds»
import «AMPUNI-total-polynomial-function»
import Lean.Util.CollectAxioms

namespace BQPBudgetAudit

/-- The global budget premise in the old conditional PP headline is impossible.
This does not refute BQP ⊆ PP: the repaired construction handles short inputs separately. -/
theorem no_global_checker_budget (hh : List Bool → Nat) (k : Nat) :
    ¬ (∀ x : List Bool, 3 * hh x + 7 ≤ x.length ^ k) := by
  intro h
  have hb := h [false]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, one_pow] at hb
  omega

end BQPBudgetAudit

open Lean Elab Command in
run_cmd do
  for name in #[``ShiTMTotalPolynomialClocked.total_polynomial,
      ``ShiTMTotalPolynomialClocked.valid_run_polynomial,
      ``ShiTMTotalFunction.function_of_total_polynomial] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected reused QMA axiom {ax} in {name}"
    logInfo m!"BQP_QMA_MACHINERY_CHECKED {name}; axioms {axioms}"

open Lean Elab Command in
run_cmd do
  let axioms ← collectAxioms ``BQPBudgetAudit.no_global_checker_budget
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected budget diagnostic axiom {ax}"
  logInfo m!"BQP_GLOBAL_BUDGET_REFUTED; axioms {axioms}"
