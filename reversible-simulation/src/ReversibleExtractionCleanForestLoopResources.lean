import ReversibleExtractionCleanForestLoopPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The same spent-slot invariant bounds every counter at the end of the recursive emitter. -/
theorem extractionCleanForestDescending_budget (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound k spent : Nat) (cs : ExtractionForestRegister → Nat)
    (h : ExtractionCleanForestBudget tm bound spent cs) (hk : spent+k ≤ bound) :
    ExtractionCleanForestBudget tm bound (spent+k)
      (descendingTemplateCounters (extractionCleanForestStepTemplate tm e stride backward) 26 k cs) := by
  induction k generalizing spent cs with
  | zero => simpa [descendingTemplateCounters] using h
  | succ k ih =>
    let next := Function.update cs (26 : ExtractionForestRegister) k
    let after := (extractionCleanForestStepTemplate tm e stride backward).counters next
    have hn := extractionCleanForestBudget_update tm bound spent k cs h (by omega)
    have ha := extractionCleanForestBudget_step tm e stride backward bound spent next hn
    have hi := ih (spent+1) after ha (by omega)
    change ExtractionCleanForestBudget tm bound (spent+(k+1)) (descendingTemplateCounters _ 26 k after)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

theorem extractionCleanForestLoopTemplate_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionCleanForestLoopTemplate tm e stride backward).CounterBound bound ∧
      (extractionCleanForestLoopTemplate tm e stride backward).PolynomiallyTimed bound := by
  refine ⟨?_,extractionCleanForestLoopTemplate_polynomial tm e stride backward bound⟩
  let D := 10+Fintype.card (Option (MachineSymbol tm))*7
  let layers := Polynomial.C 37*(Polynomial.C 1+(bound+Polynomial.C 1)*Polynomial.C D)+Polynomial.C 1
  let global := bound+bound*(layers+bound+Polynomial.C 2)
  refine ⟨global,?_⟩
  intro n cs hb q
  let B := bound.eval n
  have hg : global.eval n=B+B*(extractionForestLayerIncrementBound tm B+B+2) := by
    simp [global,layers,B,D,extractionForestLayerIncrementBound,extractionBitBound]
  have hi := extractionCleanForestDescending_budget tm e stride backward B (cs 26) 0 cs
    (extractionCleanForestBudget_initial tm B cs hb) (by simpa using hb 26)
  have hu := extractionCleanForestBudget_uniform tm B (cs 26) _ (by simpa using hi) (hb 26)
  change Function.update (descendingTemplateCounters _ 26 (cs 26) cs) 26 0 q ≤ global.eval n
  by_cases hq : q=26
  · subst q; simp
  · rw [Function.update_of_ne hq,hg]
    exact hu q

end ShiReversibleGenerator
