import ReversibleExtractionInputBinding
import ReversibleExtractionTermPayloadAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Values returned by the three actual binders give every original term input its concrete wire address. -/
theorem extractionInputBindingTemplate_inputs (tm : Turing.FinTM2) (stride : Nat)
    (cs : ExtractionTermRegister → Nat) (hp : cs 10=cs 2-1) (hv : cs 4=cs 1-cs 2-1) :
    let after := (extractionInputBindingTemplate tm stride).counters cs
    ∀ i,(extractionBoundInputs tm stride i).eval (Function.update after 3 (2*after 2))=
      cs 11+stride*naturalConfigurationAddress tm (cs 0) (extractionTermNaturalInput tm (cs 2) (cs 1) i) := by
  intro after i
  dsimp only [after]
  cases i with
  | inl i =>
    by_cases hi : i.val=0
    all_goals simp [extractionBoundInputs,SymbolicWire.eval,extractionInputBindingTemplate,
      sequenceProgramTemplate,coordinateBindingProgramTemplate,stridedTickCoordinateAddress,
      extractionInputBindingRegisters,tickSymbolicCoordinateEval,TickIndexExpr.eval,
      extractionTermNaturalInput,hi,hp,hv]
  | inr a =>
    simp [extractionBoundInputs,SymbolicWire.eval,extractionInputBindingTemplate,
      sequenceProgramTemplate,coordinateBindingProgramTemplate,stridedTickCoordinateAddress,
      extractionInputBindingRegisters,tickSymbolicCoordinateEval,TickIndexExpr.eval,
      extractionTermNaturalInput,extractionFirstSymbol,naturalConfigurationAddress,hp,hv]
    ring

end ShiReversibleGenerator
