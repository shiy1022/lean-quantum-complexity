import ReversibleMachineFinishedRawCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleGateBridge

noncomputable def castLayered {a b : Nat} (h : a=b) (gs : ShiShallow.Layered a) : ShiShallow.Layered b := h ▸ gs

theorem castLayered_encCirc {a b : Nat} (h : a=b) (gs : ShiShallow.Layered a) :
    ShiBQP.encCirc (castLayered h gs)=ShiBQP.encCirc gs := by cases h; rfl

theorem castLayered_length {a b : Nat} (h : a=b) (gs : ShiShallow.Layered a) :
    (castLayered h gs).length=gs.length := by cases h; rfl

noncomputable def machineSemanticWireCount (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) : Nat :=
  let cap := n+budget*machinePushBound tm+1
  n+paddedFinishedSize (initialForest tm e₀ cap n) (tickForest tm cap) (extractionForest tm e₁ cap)
    17 (tickSizeBound tm) (extractionBitBound tm cap) budget+(extractionForest tm e₁ cap).length

theorem machineSemanticWireCount_eq (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (n budget : Nat) :
    machineSemanticWireCount tm e₀ e₁ n budget=
      n+(paddedMachineWorkspace tm n budget+(2*(n+budget*machinePushBound tm+1)+1)-1+1) := by
  unfold machineSemanticWireCount
  dsimp only
  rw [paddedRawOutputCircuit_workspace,extractionForest_length]
  omega

/-- The original semantic circuit packaged in the established family's mandatory-ancilla convention. -/
noncomputable def paddedMachineUniformFamily (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) : ShiClass.Family where
  anc n := paddedMachineWorkspace tm n ((n+c)^d)+(2*(n+(n+c)^d*machinePushBound tm+1)+1)-1
  circ n := castLayered (machineSemanticWireCount_eq tm e₀ e₁ n ((n+c)^d))
    (paddedMachineQuantumCircuit tm e₀ e₁ n ((n+c)^d))
  out n := ⟨n+paddedMachineWorkspace tm n ((n+c)^d),by omega⟩

end ShiReversibleGenerator
