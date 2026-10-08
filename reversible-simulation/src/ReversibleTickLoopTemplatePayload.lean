import ReversibleTickSymbolRowDescendingPayload
import ReversibleTickSymbolRowAscendingPayload
import ReversibleTickAscendingLoopTemplate
import ReversibleTickDescendingLoopTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowDescendingTemplate_payload (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)).bytes cs =
      tickSymbolRowDescendingBytes tm stack inputStride strideBound backward (cs (.inl 0)) (cs (.inl 1))
        (cs (tickTraversalSpare tm 2)) (cs (.inl 2)) := by
  let p := tickSymbolRowTemplate tm stack inputStride strideBound backward
  let s : CounterCfg _ (p.Labels (Fin 3)) := ⟨none,cs,[]⟩
  have h := tickSymbolRowDescendingResult_output tm stack inputStride strideBound backward (cs (.inl 2)) s
  change (descendingResult (templateDescendingBody p (.inl 2)) (cs (.inl 2)) s).output = _ at h
  rw [descendingTemplateResult_output] at h
  simpa only [s,descendingProgramTemplate,List.append_nil] using h

theorem tickSymbolRowAscendingTemplate_payload (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).bytes cs =
      tickSymbolRowAscendingBytes tm stack inputStride strideBound backward (cs (.inl 0)) (cs (.inl 1))
        (cs (tickTraversalSpare tm 2)) (cs (.inl 2)) (cs (tickTraversalSpare tm 0)) := by
  let p := tickSymbolRowAscendingBody tm stack inputStride strideBound backward
  let s : CounterCfg _ (p.Labels (Fin 3)) := ⟨none,cs,[]⟩
  have h := tickSymbolRowAscendingResult_output tm stack inputStride strideBound backward (cs (tickTraversalSpare tm 0)) s
  change (descendingResult (templateDescendingBody p (tickTraversalSpare tm 0)) (cs (tickTraversalSpare tm 0)) s).output = _ at h
  rw [descendingTemplateResult_output] at h
  simpa only [s,tickSymbolRowAscendingTemplate,descendingProgramTemplate,List.append_nil] using h

end ShiReversibleGenerator
