import ReversibleExtractionBoundTermPrinter
import ReversibleExtractionInputSetupPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The complete term printer's polynomial clock includes actual cleanup, index computation and every input binding. -/
theorem extractionBoundTermPrinterTemplate_polynomial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionBoundTermPrinterTemplate tm e stride backward).PolynomiallyTimed bound := by
  obtain ⟨budget,hsetup,hbudget⟩ := extractionInputSetupTemplate_resources tm stride bound
  exact sequenceProgramTemplate_polynomial _ _ bound budget hsetup
    (fun n cs hb _ => hbudget n cs hb)
    (extractionTermDispatchTemplate_polynomial tm e backward _ budget)

/-- Only the guard and printer scratch that the setup does not own need to be initially zero. -/
theorem extractionBoundTermPrinterTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionTermRegister → Nat)
    (h5 : cs 5=0) (h6 : cs 6=0) (h17 : cs 17=0) :
    (extractionBoundTermPrinterTemplate tm e stride backward).ready cs := by
  refine ⟨extractionInputSetupTemplate_ready tm stride cs,?_⟩
  rw [extractionTermDispatchTemplate_ready]
  have frame : ∀ q ∈ ([5,6,17] : List ExtractionTermRegister),
      (extractionInputSetupTemplate tm stride).counters cs q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq | hq | hq
    all_goals subst q
    all_goals exact extractionInputSetupTemplate_frame tm stride cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨(frame 5 (by simp)).trans h5,(frame 6 (by simp)).trans h6,?_,(frame 17 (by simp)).trans h17⟩
  simp [extractionInputSetupTemplate,sequenceProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,
    extractionIndexSetupTemplate_counters,extractionInputBindingTemplate,coordinateBindingProgramTemplate,
    extractionInputBindingRegisters]

end ShiReversibleGenerator
