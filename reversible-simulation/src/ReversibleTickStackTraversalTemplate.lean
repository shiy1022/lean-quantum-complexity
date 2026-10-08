import ReversibleCleanupProgramTemplate
import ReversibleTickLoopTemplatePayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Actual traversal setup, fixed symbol rows, and control-counter cleanup for one stack. -/
noncomputable def tickStackTraversalTemplate (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :
    CounterProgramTemplate (FixedLeafRegister (tickTraversalSupply tm)) :=
  let clear := cleanupProgramTemplate [.inl 2,tickTraversalSpare tm 0]
  if backward then
    sequenceProgramTemplate (cleanupProgramTemplate [.inl 2])
      (sequenceProgramTemplate (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5))
        (sequenceProgramTemplate (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward) clear))
  else
    sequenceProgramTemplate (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5))
      (sequenceProgramTemplate
        (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)) clear)

theorem tickStackTraversalTemplate_embeds (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).Embeds := by
  unfold tickStackTraversalTemplate
  split <;> (repeat' apply sequenceProgramTemplate_embeds)
  all_goals first
    | exact cleanupProgramTemplate_embeds _
    | exact counterCopyProgramTemplate_embeds _ _ _
    | exact tickSymbolRowAscendingTemplate_embeds tm stack inputStride strideBound backward
    | exact descendingProgramTemplate_embeds _ _ (tickSymbolRowTemplate_embeds tm stack inputStride strideBound backward)

theorem tickStackTraversalTemplate_run (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).Runs := by
  unfold tickStackTraversalTemplate
  split <;> (repeat' apply sequenceProgramTemplate_run)
  all_goals first
    | exact cleanupProgramTemplate_embeds _
    | exact cleanupProgramTemplate_run _
    | exact counterCopyProgramTemplate_embeds _ _ _
    | exact counterCopyProgramTemplate_run _ _ _ (by simp [tickTraversalSpare])
        (by simp [tickTraversalSpare]) (by simp [tickTraversalSpare])
    | exact tickSymbolRowAscendingTemplate_embeds tm stack inputStride strideBound backward
    | exact tickSymbolRowAscendingTemplate_run tm stack inputStride strideBound backward
    | exact descendingProgramTemplate_embeds _ _ (tickSymbolRowTemplate_embeds tm stack inputStride strideBound backward)
    | exact descendingProgramTemplate_run _ _ (tickSymbolRowTemplate_embeds tm stack inputStride strideBound backward)
        (tickSymbolRowTemplate_run tm stack inputStride strideBound backward)

end ShiReversibleGenerator
