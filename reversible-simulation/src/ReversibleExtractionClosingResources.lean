import ReversibleExtractionBoundClosingPrinter
import ReversibleExtractionTermSizeBudget
import ReversibleCounterAffineExitBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionClosingSetupTemplate_resources (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, (extractionClosingSetupTemplate tm).PolynomiallyTimed bound ∧
      ∀ n (cs : ExtractionTermRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
        ∀ q,(extractionClosingSetupTemplate tm).counters cs q ≤ budget.eval n := by
  let middle := Polynomial.C 2*bound+Polynomial.C (10+Fintype.card (Option (MachineSymbol tm))*7)
  refine ⟨Polynomial.C 2*middle,?_,?_⟩
  · unfold extractionClosingSetupTemplate
    apply sequenceProgramTemplate_polynomial _ _ bound middle
    · exact extractionTermSizeProgramTemplate_polynomial tm bound
    · intro n cs hb hr
      exact extractionTermSizeProgramTemplate_budget tm bound n cs hb
    · unfold extractionClosingPointerTemplate
      apply sequenceProgramTemplate_polynomial _ _ middle middle
      · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ middle
      · intro n cs hb hr
        exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
      · apply sequenceProgramTemplate_polynomial _ _ middle (Polynomial.C 2*middle)
        · exact counterAffineAccumulationProgramTemplate_polynomial _ _ middle
        · intro n cs hb hr q
          simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
            counterAffineUnitAccumulationProgramTemplate_budget (12 : ExtractionTermRegister) 21 7 cs (middle.eval n) hb q
        · apply sequenceProgramTemplate_polynomial _ _ (Polynomial.C 2*middle) (Polynomial.C 2*middle)
          · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
          · intro n cs hb hr
            exact counterAffineUnitCopyProgramTemplate_budget _ _ _ _ cs _ hb
          · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ _
  · intro n cs hb q
    have h0 := extractionTermSizeProgramTemplate_budget tm bound n cs hb
    have h1 := counterAffineUnitCopyProgramTemplate_budget (18 : ExtractionTermRegister) 21 7 0 _ _ h0
    have h2 := counterAffineUnitAccumulationProgramTemplate_budget (12 : ExtractionTermRegister) 21 7 _ _ h1
    have h3 := counterAffineUnitCopyProgramTemplate_budget (21 : ExtractionTermRegister) 19 7 4 _ _ h2
    have h4 := counterAffineUnitCopyProgramTemplate_budget (20 : ExtractionTermRegister) 21 7 3 _ _ h3
    simpa only [extractionClosingSetupTemplate,extractionClosingPointerTemplate,sequenceProgramTemplate,Polynomial.eval_mul,Polynomial.eval_C,middle] using h4 q

theorem extractionBoundClosingPrinterTemplate_polynomial (tm : Turing.FinTM2) (backward : Bool)
    (bound : Polynomial Nat) : (extractionBoundClosingPrinterTemplate tm backward).PolynomiallyTimed bound := by
  obtain ⟨budget,hsetup,hbudget⟩ := extractionClosingSetupTemplate_resources tm bound
  exact sequenceProgramTemplate_polynomial _ _ bound budget hsetup
    (fun n cs hb _ => hbudget n cs hb)
    (extractionClosingPrinterTemplate_polynomial _ _ _ _ budget)

end ShiReversibleGenerator
