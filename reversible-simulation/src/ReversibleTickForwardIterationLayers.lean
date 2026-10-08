import ReversibleTickForwardIterationTemplate
import ReversibleTickForwardStepClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Reserve the exact per-tick layer count for every remaining real iteration. -/
def TickForwardIterationLayerBudget (tm : Turing.FinTM2) (bound wireBound capacity layers count : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) : Prop :=
  TickForwardIterationBudget tm bound wireBound capacity count cs ∧
    cs (.inl 9)+count*tickForestLayerCount tm capacity ≤ layers

theorem TickForwardIterationLayerBudget.remaining_update (tm : Turing.FinTM2)
    (bound wireBound capacity layers count value : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickForwardIterationLayerBudget tm bound wireBound capacity layers count cs)
    (hv : value ≤ wireBound) :
    TickForwardIterationLayerBudget tm bound wireBound capacity layers count
      (Function.update cs (tickTraversalSpare tm 3) value) := by
  refine ⟨TickForwardIterationBudget.remaining_update tm bound wireBound capacity count value cs hs.1 hv,?_⟩
  simpa [tickTraversalSpare] using hs.2

/-- Emitting one forest consumes exactly its reserved layers. -/
theorem tickForwardIterationLayerBudget_next (tm : Turing.FinTM2)
    (bound wireBound capacity layers k : Nat) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickForwardIterationLayerBudget tm bound wireBound capacity layers (k+1) cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    TickForwardIterationLayerBudget tm bound wireBound capacity layers k
      ((tickForwardStepTemplate tm (bound+1) bound).counters
        (Function.update cs (tickTraversalSpare tm 3) k)) := by
  refine ⟨tickForwardIterationBudget_next tm bound wireBound capacity k cs hs.1 hc hsize,?_⟩
  rw [tickForwardStepTemplate_count]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
    Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3)]
  rw [hs.1.2.2.1]
  have h := hs.2
  simp only [Nat.add_mul,Nat.one_mul] at h
  omega

end ShiReversibleGenerator
