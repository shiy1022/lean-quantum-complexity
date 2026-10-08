import ReversibleTickStackListTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The complete fixed stack schedule increases the emitted layer count linearly in capacity. -/
theorem tickStackListTemplate_layer_bound (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hsize : tickSizeBound tm ≤ strideBound) :
    (tickStackListTemplate tm stackOrder inputStride strideBound backward).counters cs (.inl 9) ≤
      cs (.inl 9)+cs (.inl 1)*((stackOrder.map (fun k => (tickSymbolRowKinds tm k).length)).sum*(37*tickSizeBound tm+1)) := by
  induction stackOrder generalizing cs with
  | nil => simp [tickStackListTemplate,listProgramTemplate,identityProgramTemplate]
  | cons k stackOrder ih =>
    let after := (tickStackTraversalTemplate tm k inputStride strideBound backward).counters cs
    have hf := tickStackTraversalTemplate_final_bounds tm k inputStride strideBound backward wireBound (cs (.inl 9))
      cs hr hb hw le_rfl hsize
    have ht := ih after hf.2.2.1 hf.1 hf.2.1
    have hc : after (.inl 1)=cs (.inl 1) :=
      tickStackTraversalTemplate_control_frame tm k inputStride strideBound backward cs 1 (by decide) (by decide)
    rw [hc] at ht
    change (tickStackListTemplate tm stackOrder inputStride strideBound backward).counters after (.inl 9) ≤ _
    calc
      _ ≤ after (.inl 9)+cs (.inl 1)*((stackOrder.map (fun k => (tickSymbolRowKinds tm k).length)).sum*(37*tickSizeBound tm+1)) := ht
      _ ≤ (cs (.inl 9)+cs (.inl 1)*((tickSymbolRowKinds tm k).length*(37*tickSizeBound tm+1)))+
          cs (.inl 1)*((stackOrder.map (fun k => (tickSymbolRowKinds tm k).length)).sum*(37*tickSizeBound tm+1)) :=
        Nat.add_le_add_right hf.2.2.2 _
      _ = _ := by
        simp only [List.map_cons,List.sum_cons]
        ring

end ShiReversibleGenerator
