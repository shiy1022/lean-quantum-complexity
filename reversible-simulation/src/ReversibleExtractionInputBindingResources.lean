import ReversibleExtractionInputBinding
import ReversibleCoordinateBindingResourceBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Three real binders have polynomial exit counters and polynomial instruction count. -/
theorem extractionInputBindingTemplate_resources (tm : Turing.FinTM2) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat, ∀ n (cs : ExtractionTermRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
      (∀ q,(extractionInputBindingTemplate tm stride).counters cs q ≤ budget.eval n) ∧
      (extractionInputBindingTemplate tm stride).steps cs ≤ clock.eval n := by
  let p := coordinateBindingProgramTemplate tm (extractionInputBindingRegisters 10 19) stride
    (.inr ((tm.k₁,.position),none))
  let q := coordinateBindingProgramTemplate tm (extractionInputBindingRegisters 2 20) stride
    (.inr ((tm.k₁,.position),none))
  let r := coordinateBindingProgramTemplate tm (extractionInputBindingRegisters 4 21) stride
    (.inr ((tm.k₁,.position),extractionFirstSymbol tm))
  obtain ⟨middle1,clock1,h1⟩ := coordinateBindingProgramTemplate_resources tm
    (extractionInputBindingRegisters 10 19) stride (.inr ((tm.k₁,.position),none))
    (by constructor <;> decide) bound
  obtain ⟨middle2,clock2,h2⟩ := coordinateBindingProgramTemplate_resources tm
    (extractionInputBindingRegisters 2 20) stride (.inr ((tm.k₁,.position),none))
    (by constructor <;> decide) middle1
  obtain ⟨budget,clock3,h3⟩ := coordinateBindingProgramTemplate_resources tm
    (extractionInputBindingRegisters 4 21) stride (.inr ((tm.k₁,.position),extractionFirstSymbol tm))
    (by constructor <;> decide) middle2
  have htail := sequenceProgramTemplate_resources q r middle1 middle2 budget clock2 clock3 h2 h3
  refine ⟨budget,clock1+(clock2+clock3),?_⟩
  exact sequenceProgramTemplate_resources p (sequenceProgramTemplate q r) bound middle1 budget clock1
    (clock2+clock3) h1 htail

theorem extractionInputBindingTemplate_polynomial (tm : Turing.FinTM2) (stride : Nat) (bound : Polynomial Nat) :
    (extractionInputBindingTemplate tm stride).PolynomiallyTimed bound := by
  obtain ⟨budget,clock,h⟩ := extractionInputBindingTemplate_resources tm stride bound
  exact ⟨clock,fun n cs hb _ => (h n cs hb).2⟩

end ShiReversibleGenerator
