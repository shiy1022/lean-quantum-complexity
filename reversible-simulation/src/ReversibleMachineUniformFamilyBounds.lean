import ReversibleMachineUniformFamilyData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleGateBridge

theorem castLayered_layerOk {a b : Nat} (h : a=b) (gs : ShiShallow.Layered a)
    (hg : ∀ l ∈ gs,ShiShallow.LayerOk l) : ∀ l ∈ castLayered h gs,ShiShallow.LayerOk l := by
  cases h
  exact hg

theorem paddedMachineUniformFamily_wellFormed (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) :
    ShiBQP.WellFormed (paddedMachineUniformFamily tm e₀ e₁ c d) := by
  intro n
  exact castLayered_layerOk _ _ (paddedMachineQuantumCircuit_layerOk tm e₀ e₁ n ((n+c)^d))

/-- One natural-coefficient polynomial bounds both the actual family depth and ancilla count. -/
theorem paddedMachineUniformFamily_polyBounded (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c d : Nat) :
    ShiBQP.PolyBounded (paddedMachineUniformFamily tm e₀ e₁ c d) := by
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  obtain ⟨depth,hd⟩ := paddedMachineQuantumCircuit_depth_polynomial tm e₀ e₁ time
  obtain ⟨wires,hw⟩ := paddedRawOutputCircuit_wires_polynomial tm time
  have ht : ∀ n,time.eval n=(n+c)^d := by intro n; simp [time]
  refine ⟨depth+wires,?_,?_⟩
  · intro n
    have h := hd n
    rw [ht] at h
    change (castLayered _ _).length ≤ _
    rw [castLayered_length,Polynomial.eval_add]
    exact h.trans (Nat.le_add_right _ _)
  · intro n
    have h := hw n
    rw [ht] at h
    change paddedMachineWorkspace tm n ((n+c)^d)+(2*(n+(n+c)^d*machinePushBound tm+1)+1)-1 ≤ _
    rw [Polynomial.eval_add]
    omega

end ShiReversibleGenerator
