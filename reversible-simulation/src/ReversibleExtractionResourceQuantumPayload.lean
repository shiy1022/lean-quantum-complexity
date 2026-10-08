import ReversibleExtractionResourcePolynomialRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The pure payload printed from raw length is the original finite-wire extraction circuit. -/
theorem extractionResourcePayload_quantum (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (n budget : Nat) (ht : 0 < budget) :
    let cap := n+budget*machinePushBound tm+1
    let base := n+18*configurationWidth tm cap+budget*(configurationWidth tm cap*(tickSizeBound tm+1))
    let source := base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm
    let wires := n+paddedMachineWorkspace tm n budget+(2*cap+1)
    let hin := extractionFinalSource_lt_base tm n budget ht
    let hout : base+(2*cap+1)*(extractionBitBound tm cap+1) ≤ wires :=
      (by rw [extractionForestEnd_eq_output]; exact Nat.le_add_right _ _)
    extractionResourcePayload tm e backward n budget=
      ((extractionForestQuantumLayers tm e cap source (tickSizeBound tm+1) base (extractionBitBound tm cap)
        wires (Nat.le_refl _) hin hout backward).map ShiBQP.encLayer).flatten := by
  dsimp only
  let cap := n+budget*machinePushBound tm+1
  let base := n+18*configurationWidth tm cap+budget*(configurationWidth tm cap*(tickSizeBound tm+1))
  let source := base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm
  let wires := n+paddedMachineWorkspace tm n budget+(2*cap+1)
  have hin := extractionFinalSource_lt_base tm n budget ht
  have hout : base+(2*cap+1)*(extractionBitBound tm cap+1) ≤ wires := by
    change n+18*configurationWidth tm cap+budget*(configurationWidth tm cap*(tickSizeBound tm+1))+
      (2*cap+1)*(extractionBitBound tm cap+1) ≤ n+paddedMachineWorkspace tm n budget+(2*cap+1)
    rw [extractionForestEnd_eq_output]
    exact Nat.le_add_right _ _
  exact (extractionResourceTemplate_payload_count tm e backward n budget
    (extractionResourceState tm n budget) (fun _ => rfl)).1.trans
    (extractionForestQuantumLayers_payload tm e cap source (tickSizeBound tm+1) base
      (extractionBitBound tm cap) wires (Nat.le_refl _) hin hout backward)

end ShiReversibleGenerator
