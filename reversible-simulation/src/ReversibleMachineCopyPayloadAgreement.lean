import ReversibleMachineFinishedRawCertificate
import ReversibleOutputCopyNaturalEncoding

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversible ShiReversibleTM ShiReversibleFormula ShiReversibleGateBridge

/-- Abstract metadata keeps the semantic encoding comparison independent of the resource program's implementation. -/
theorem outputCopyMasterTemplate_semantic (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat)
    (cs : OutputCopyMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r) :
    outputCopyMasterTemplate.bytes cs=
      ((substitute ((copyOut (paddedRawOutputCircuit tm e₀ e₁ n budget).read).map flatInstruction)).map ShiBQP.encLayer).flatten := by
  have h := outputCopyResource_quantum_payload tm n budget cs hpull
  dsimp only at h
  rw [stridedOutputCopyLayers_encoding] at h
  obtain ⟨h4,h9,h10,h11,h5⟩ := outputCopyResource_metadata tm n budget cs hpull
  unfold paddedRawOutputCircuit
  rw [paddedFinishedCircuit_copyOut_strided]
  rw [stridedOutputCopyLayers_encoding]
  simp only [h4,h9,h10,h11] at h
  apply h.trans
  simp only [initialForest_length,extractionForest_length,Fin.coe_cast,paddedRawOutputCircuit_workspace,
    show (17 : Nat)+1=18 from rfl]

/-- The actual copy printer's bytes are exactly the copy block in the original semantic circuit. -/
theorem outputCopyResourcePayload_semantic (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    outputCopyResourcePayload tm n budget=
      ((substitute ((copyOut (paddedRawOutputCircuit tm e₀ e₁ n budget).read).map flatInstruction)).map ShiBQP.encLayer).flatten :=
  outputCopyMasterTemplate_semantic tm e₀ e₁ n budget (outputCopyResourceState tm n budget) (fun _ => rfl)

end ShiReversibleGenerator
