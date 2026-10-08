import ReversibleExtractionResourceSetupMetadata
import ReversibleOutputCopyResourceMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Scalar coordinates supplied by the actual resource prelude in the extraction register file. -/
theorem extractionResource_metadata (tm : Turing.FinTM2) (n time : Nat)
    (cs : ExtractionMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n time) r) :
    cs (.inl 2)=n+time*machinePushBound tm+1 ∧
      cs (.inl 4)=extractionBitBound tm (n+time*machinePushBound tm+1)+1 ∧
      cs (.inl 8)=configurationWidth tm (n+time*machinePushBound tm+1)*(tickSizeBound tm+1) ∧
      cs (.inl 9)=2*(n+time*machinePushBound tm+1)+1 ∧
      cs (.inl 11)=n+18*configurationWidth tm (n+time*machinePushBound tm+1)+
        time*(configurationWidth tm (n+time*machinePushBound tm+1)*(tickSizeBound tm+1)) ∧
      cs (.inl 10)=n+paddedMachineWorkspace tm n time := by
  let old : OutputCopyMasterRegister → Nat := Sum.elim (fun r => cs (.inl r)) (fun _ => 0)
  have ho : ∀ r,old (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n time) r := hpull
  obtain ⟨h4,h9,h10,h11,_⟩ := outputCopyResource_metadata tm n time old ho
  have h2 : cs (.inl 2)=n+time*machinePushBound tm+1 := by
    simpa [operationResult,workspaceOperations,GeneratorOperation.apply,AffineAtom.apply,workspaceInitial] using hpull 2
  have h8 : cs (.inl 8)=configurationWidth tm (n+time*machinePushBound tm+1)*(tickSizeBound tm+1) := by
    simpa [operationResult,workspaceOperations,GeneratorOperation.apply,AffineAtom.apply,workspaceInitial,Nat.mul_comm] using hpull 8
  refine ⟨h2,h4,h8,h9,?_,h10⟩
  simpa [old,Nat.mul_comm] using h11

/-- No free output-coordinate premise remains after the real finite resource setup. -/
theorem extractionResourceSetup_coordinates (tm : Turing.FinTM2) (backward : Bool) (n time : Nat)
    (cs : ExtractionMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n time) r) :
    let cap := n+time*machinePushBound tm+1
    let base := n+18*configurationWidth tm cap+time*(configurationWidth tm cap*(tickSizeBound tm+1))
    let after := (extractionResourceSetupTemplate tm backward).counters cs
    after (.inr 0)=cap ∧ after (.inr 1)=(if backward then 0 else (2*cap+1)-1) ∧
      after (.inr 11)=base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm ∧
      after (.inr 18)=(if backward then base else n+paddedMachineWorkspace tm n time) ∧
      after (.inr 26)=2*cap+1 ∧ after (.inr 27)=extractionBitBound tm cap ∧ after (.inr 16)=0 := by
  obtain ⟨h2,h4,h8,h9,h11,h10⟩ := extractionResource_metadata tm n time cs hpull
  have h := extractionResourceSetupTemplate_metadata tm backward cs
  dsimp only
  simpa only [h2,h4,h8,h9,h11,h10,Nat.add_sub_cancel] using h

end ShiReversibleGenerator
