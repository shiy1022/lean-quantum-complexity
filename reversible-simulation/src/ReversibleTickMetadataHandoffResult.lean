import ReversibleTickMetadataHandoffTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The real prelude result and finite handoff establish the retained metadata used by both history emitters. -/
theorem tickResourcePrelude_handoff_result (tm : Turing.FinTM2) (n time : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hpull : ∀ r,cs (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n time) r) :
    let final := (tickMetadataHandoffTemplate tm).counters cs
    fixedGuardedEmitterReady (tickTraversalSupply tm) final ∧
      final (tickTraversalSpare tm 6)=n ∧ final (tickTraversalSpare tm 7)=time ∧
      final (.inl 1)=n+time*machinePushBound tm+1 ∧
      final (tickTraversalSpare tm 1)=n+18*configurationWidth tm (n+time*machinePushBound tm+1)+
        time*(configurationWidth tm (n+time*machinePushBound tm+1)*(tickSizeBound tm+1)) ∧
      final (.inl 0)=n ∧ final (.inl 9)=0 := by
  obtain ⟨hraw,htime,hcap,hend,hscratch,hbuffer⟩ := tickResourcePrelude_metadata tm n time cs hpull
  obtain ⟨h6,h7,h1,hc,h0,h9⟩ := tickMetadataHandoffTemplate_metadata tm cs
  refine ⟨tickMetadataHandoffTemplate_scratch_ready tm cs hscratch,h6.trans hraw,h7.trans htime,
    hc.trans hcap,h1.trans hend,h0.trans hraw,h9⟩

end ShiReversibleGenerator
