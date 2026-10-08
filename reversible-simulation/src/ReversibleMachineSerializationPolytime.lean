import ReversibleMachineSerializationProgram
import ReversibleCleanTemplatePolytime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The actual seven-phase serializer, established header computation and complete cleanup give a genuine polynomial-time TM2 generator from raw input length. -/
theorem machineLengthSerialization_polytime (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) (hc : 0<c) :
    Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun xs => machineLengthSerialization tm e₀ e₁ c d xs.length)) := by
  classical
  obtain ⟨p,he,hr,hready,hbytes,hresources⟩ := machineSerializationProgramTemplate_exists tm e₀ e₁ c d hc
  have hp := cleanTemplate_polytime p (.inl 0) he hr
    (by intro n; apply hready; simp [Function.update_apply])
    (hresources Polynomial.X).1 (hresources Polynomial.X).2
  have hf : (fun xs : List Bool => p.bytes (Function.update (fun _ => 0) (.inl 0) xs.length))=
      (fun xs => machineLengthSerialization tm e₀ e₁ c d xs.length) := by
    funext xs
    have h := hbytes (Function.update (fun _ => 0) (.inl 0) xs.length)
      (by simp [Function.update_apply])
    simpa only [Function.update_self] using h
  rw [hf] at hp
  exact hp

end ShiReversibleGenerator
