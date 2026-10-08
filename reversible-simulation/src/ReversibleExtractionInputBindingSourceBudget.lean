import ReversibleCoordinateBindingSourceBudget
import ReversibleExtractionInputBinding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- All three actual input bindings have a fixed polynomial budget using only their source metadata. -/
theorem extractionInputBindingTemplate_source_budget (tm : Turing.FinTM2) (stride : Nat)
    (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : ExtractionTermRegister → Nat),
      (∀ q ∈ ([0,2,4,10,11] : List ExtractionTermRegister),cs q ≤ bound.eval n) →
      ∀ q ∈ ([19,20,21] : List ExtractionTermRegister),
        (extractionInputBindingTemplate tm stride).counters cs q ≤ budget.eval n := by
  obtain ⟨b19,h19⟩ := stridedTickCoordinateAddress_source_polynomial tm
    (extractionInputBindingRegisters 10 19) stride (.inr ((tm.k₁,.position),none)) bound
  obtain ⟨b20,h20⟩ := stridedTickCoordinateAddress_source_polynomial tm
    (extractionInputBindingRegisters 2 20) stride (.inr ((tm.k₁,.position),none)) bound
  obtain ⟨b21,h21⟩ := stridedTickCoordinateAddress_source_polynomial tm
    (extractionInputBindingRegisters 4 21) stride (.inr ((tm.k₁,.position),extractionFirstSymbol tm)) bound
  refine ⟨b19+b20+b21,?_⟩
  intro n cs hb q hq
  have hi := hb 11 (by simp)
  have hc := hb 0 (by simp)
  have hp := hb 10 (by simp)
  have hl := hb 2 (by simp)
  have hv := hb 4 (by simp)
  have ha := h19 n cs hi hc hp
  have hd := h20 n cs hi hc hl
  have he := h21 n cs hi hc hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  all_goals simp only [Polynomial.eval_add]
  all_goals simp [extractionInputBindingTemplate,sequenceProgramTemplate,coordinateBindingProgramTemplate,
    extractionInputBindingRegisters,stridedTickCoordinateAddress] at ha hd he ⊢
  all_goals omega

end ShiReversibleGenerator
