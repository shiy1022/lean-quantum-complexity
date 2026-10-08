import ReversibleMachineRawDecomposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

noncomputable def rawNodesPayload (backward : Bool) (nodes : List RawAssignment) : List Bool :=
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

theorem initializerResourcePayload_raw (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (c d n : Nat) :
    initializerResourcePayload tm e backward c d n=
      rawNodesPayload backward (initializationRawNodes tm e (n+(n+c)^d*machinePushBound tm+1) n) := by
  unfold initializerResourcePayload rawNodesPayload
  rw [←initializationQuantumLayers_payload]
  simp only [initializationCapacityPolynomial,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_C]

theorem tickResourcePayload_raw (tm : Turing.FinTM2) (backward : Bool) (time : Polynomial Nat) (n : Nat) :
    tickResourcePayload tm backward time n=
      rawNodesPayload backward (tickStridedHistoryRawNodes tm (n+time.eval n*machinePushBound tm+1)
        (n+17) 18 (n+18*configurationWidth tm (n+time.eval n*machinePushBound tm+1))
        (tickSizeBound tm) (time.eval n)) := by
  cases backward <;> simp only [tickResourcePayload,Bool.false_eq_true,if_false,if_true]
  · unfold tickResourceForwardPayload
    rw [←tickStridedHistoryQuantumLayers_payload]
    simp only [tickRuntimeCapacityPolynomial_eval,rawNodesPayload,Bool.false_eq_true,if_false]
  · unfold tickResourceInversePayload
    rw [←tickStridedHistoryQuantumLayers_payload]
    simp only [tickRuntimeCapacityPolynomial_eval,rawNodesPayload,if_true]

theorem extractionResourcePayload_raw (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (n budget : Nat) :
    let cap := n+budget*machinePushBound tm+1
    let base := n+18*configurationWidth tm cap+budget*(configurationWidth tm cap*(tickSizeBound tm+1))
    extractionResourcePayload tm e backward n budget=
      rawNodesPayload backward (extractionForestRawNodes tm e cap
        (base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm)
        (tickSizeBound tm+1) base (extractionBitBound tm cap)) := by
  exact (extractionResourceTemplate_payload_count tm e backward n budget
    (extractionResourceState tm n budget) (fun _ => rfl)).1

end ShiReversibleGenerator
