import ReversibleMachineUniformFamilyData
import ReversibleMachineQuantumSerializationAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleGateBridge

/-- The actual polynomial-time serializer prints exactly the established family encoding. -/
theorem paddedMachineUniformFamily_encoding (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d n : Nat) (hc : 0<c) :
    ShiBQP.encFamilyAt (paddedMachineUniformFamily tm e₀ e₁ c d) n=
      machineLengthSerialization tm e₀ e₁ c d n := by
  unfold ShiBQP.encFamilyAt paddedMachineUniformFamily
  rw [castLayered_encCirc]
  unfold machineLengthSerialization
  rw [machineLengthPhaseBodyLayers_quantum,machineLengthPhaseBodyPayload_quantum tm e₀ e₁ c d n hc]
  simp [ShiBQP.encCirc,ShiBQP.encStr,List.append_assoc]

/-- Classical polynomial-time uniformity is derived from the actual clean finite generator, with no residual printer assumption. -/
theorem paddedMachineUniformFamily_uniform (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) (hc : 0<c) :
    ShiBQP.Uniform (paddedMachineUniformFamily tm e₀ e₁ c d) := by
  refine ⟨fun xs => machineLengthSerialization tm e₀ e₁ c d xs.length,
    machineLengthSerialization_polytime tm e₀ e₁ c d hc,?_⟩
  intro n
  simp only [ShiBQP.unary,List.length_replicate]
  exact (paddedMachineUniformFamily_encoding tm e₀ e₁ c d n hc).symm

end ShiReversibleGenerator
