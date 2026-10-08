import ReversibleOutputCopyResourcePrelude
import ReversibleTickForwardStepBudgets

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual resource endpoint supplies exactly the extraction stride, width, end and scratch. -/
theorem outputCopyResource_metadata (tm : Turing.FinTM2) (n budget : Nat)
    (cs : OutputCopyMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r) :
    cs (.inl 4)=extractionBitBound tm (n+budget*machinePushBound tm+1)+1 ∧
      cs (.inl 9)=2*(n+budget*machinePushBound tm+1)+1 ∧
      cs (.inl 10)=n+paddedMachineWorkspace tm n budget ∧
      cs (.inl 11)=n+configurationWidth tm (n+budget*machinePushBound tm+1)*18+
        budget*(configurationWidth tm (n+budget*machinePushBound tm+1)*(tickSizeBound tm+1)) ∧
      cs (.inl 5)=0 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [operationResult,workspaceOperations,GeneratorOperation.apply,AffineAtom.apply,workspaceInitial] using hpull 4
  · simpa [operationResult,workspaceOperations,GeneratorOperation.apply,AffineAtom.apply,workspaceInitial] using hpull 9
  · exact (hpull 10).trans (workspaceResult_output tm n budget)
  · exact (hpull 11).trans (workspaceResult_prepared tm n budget)
  · exact (hpull 5).trans (workspaceResult_scratch tm n budget)

/-- The physical copy region is disjoint from every extraction root, using actual layout arithmetic. -/
theorem outputCopyResource_root_layout (tm : Turing.FinTM2) (n budget : Nat)
    (cs : OutputCopyMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r) :
    0 < cs (.inl 4) ∧ 0 < cs (.inl 10) ∧
      cs (.inl 11)+cs (.inl 9)*cs (.inl 4)=cs (.inl 10) := by
  obtain ⟨h4,h9,h10,h11,_⟩ := outputCopyResource_metadata tm n budget cs hpull
  refine ⟨by rw [h4]; omega,?_,?_⟩
  · rw [h10]
    have hw := tickConfigurationWidth_positive tm (n+budget*machinePushBound tm+1)
    simp only [paddedMachineWorkspace]
    omega
  · rw [h4,h9,h10,h11]
    simp only [paddedMachineWorkspace,Nat.add_assoc]

/-- The exact generated CNOT payload follows from real prelude metadata, with no compiler premise. -/
theorem outputCopyResource_quantum_payload (tm : Turing.FinTM2) (n budget : Nat)
    (cs : OutputCopyMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r) :
    let wires := cs (.inl 10)+cs (.inl 9)
    let layout := outputCopyResource_root_layout tm n budget cs hpull
    outputCopyMasterTemplate.bytes cs=
      ((stridedOutputCopyLayers wires (cs (.inl 11)) (cs (.inl 4)) (cs (.inl 10))
        (cs (.inl 9)) layout.1 (by have h := layout.2.2; omega) (Nat.le_refl _)).map ShiBQP.encLayer).flatten := by
  dsimp only
  obtain ⟨hstride,hend,hroot⟩ := outputCopyResource_root_layout tm n budget cs hpull
  exact outputCopyMasterTemplate_strided_payload cs _ _ hstride hend hroot (Nat.le_refl _)

end ShiReversibleGenerator
