import ReversibleExtractionResourceTemplate
import ReversibleExtractionResourceLayout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Concrete setup-plus-emission prints the original machine extraction forest and its exact layer count. -/
theorem extractionResourceTemplate_payload_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (n time : Nat) (cs : ExtractionMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n time) r) :
    let cap := n+time*machinePushBound tm+1
    let base := n+18*configurationWidth tm cap+time*(configurationWidth tm cap*(tickSizeBound tm+1))
    let source := base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm
    let nodes := extractionForestRawNodes tm e cap source (tickSizeBound tm+1) base (extractionBitBound tm cap)
    (extractionResourceTemplate tm e backward).bytes cs=
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten ∧
      (extractionResourceTemplate tm e backward).counters cs (.inr 16)=
        ((extractionForest tm e cap).map (fun p => formulaElementaryLayers p+1)).sum := by
  let cap := n+time*machinePushBound tm+1
  let base := n+18*configurationWidth tm cap+time*(configurationWidth tm cap*(tickSizeBound tm+1))
  let source := base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm
  let width := 2*cap+1
  let eb := extractionBitBound tm cap
  let v := (extractionResourceSetupTemplate tm backward).counters cs
  let small := fun q : ExtractionForestRegister => v (.inr q)
  have hc := extractionResourceSetup_coordinates tm backward n time cs hpull
  change small 0=cap ∧ small 1=(if backward then 0 else width-1) ∧ small 11=source ∧
    small 18=(if backward then base else n+paddedMachineWorkspace tm n time) ∧
    small 26=width ∧ small 27=eb ∧ small 16=0 at hc
  rcases hc with ⟨h0,h1,h11,h18,h26,h27,h16⟩
  have hbytes : (extractionResourceTemplate tm e backward).bytes cs=
      (extractionCleanForestLoopTemplate tm e (tickSizeBound tm+1) backward).bytes small := by
    change (extractionCleanForestLoopTemplate tm e (tickSizeBound tm+1) backward).bytes small ++
      (extractionResourceSetupTemplate tm backward).bytes cs=_
    rw [extractionResourceSetupTemplate_bytes,List.append_nil]
  have hcount : (extractionResourceTemplate tm e backward).counters cs (.inr 16)=
      (extractionCleanForestLoopTemplate tm e (tickSizeBound tm+1) backward).counters small 16 :=
    extractionMasterLift_pull _ v 16
  have hend := extractionForestEnd_eq_output tm n time
  change base+width*(eb+1)=n+paddedMachineWorkspace tm n time at hend
  dsimp only
  cases backward
  · simp only [Bool.false_eq_true,if_false] at h1 h18
    have hj : small 1=small 26-1 := h1.trans (by rw [h26])
    have hb : small 18=base+small 26*(small 27+1) := by
      rw [h18,h26,h27]
      exact hend.symm
    have hp := extractionForwardCleanForestLoopTemplate_payload tm e (tickSizeBound tm+1) base small hj hb
    rw [h0,h26,extractionOutputRange_original,h11,h27] at hp
    have hn := extractionForwardCleanForestLoopTemplate_count tm e (tickSizeBound tm+1) small hj
    rw [h0,h26,extractionOutputRange_original,h16,Nat.zero_add] at hn
    exact ⟨hbytes.trans hp,hcount.trans hn⟩
  · simp only [if_true] at h1 h18
    have hp := extractionInverseCleanForestLoopTemplate_payload tm e (tickSizeBound tm+1) small
    rw [h0,h1,h26,extractionOutputRange_original,h11,h27,h18] at hp
    have hn := extractionInverseCleanForestLoopTemplate_count tm e (tickSizeBound tm+1) small
    rw [h0,h1,h26,extractionOutputRange_original,h16,Nat.zero_add] at hn
    exact ⟨hbytes.trans hp,hcount.trans hn⟩

end ShiReversibleGenerator
