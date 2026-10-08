import ReversibleTickInverseAdvanceIterationTemplate
import ReversibleTickInverseAdvanceClock
import ReversibleTickForwardIterationLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Emitting one forest consumes exactly its reserved layers. -/
theorem tickInverseAdvanceIterationLayerBudget_next (tm : Turing.FinTM2)
    (bound wireBound capacity layers k : Nat) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickForwardIterationLayerBudget tm bound wireBound capacity layers (k+1) cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    TickForwardIterationLayerBudget tm bound wireBound capacity layers k
      ((tickInverseAdvanceStepTemplate tm (bound+1) bound).counters
        (Function.update cs (tickTraversalSpare tm 3) k)) := by
  refine ⟨tickInverseAdvanceIterationBudget_next tm bound wireBound capacity k cs hs.1 hc hsize,?_⟩
  rw [tickInverseAdvanceStepTemplate_count]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
    Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3)]
  rw [hs.1.2.2.1]
  have h := hs.2
  simp only [Nat.add_mul,Nat.one_mul] at h
  omega

end ShiReversibleGenerator
