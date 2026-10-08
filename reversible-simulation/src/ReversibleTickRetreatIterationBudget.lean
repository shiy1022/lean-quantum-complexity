import ReversibleTickRetreatStepBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The current slice is exactly `count` slices above the retained boundary slice. -/
def TickRetreatIterationBudget (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstInput firstOutput count : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) : Prop :=
  fixedGuardedEmitterReady (tickTraversalSupply tm) cs ∧ CounterBudget cs (.inl 9) wireBound ∧
    cs (.inl 1)=capacity ∧ TickWindowBudget tm (bound+1) bound wireBound cs ∧ count ≤ wireBound ∧
    cs (.inl 0)=firstInput+count*(configurationWidth tm capacity*(bound+1)) ∧
    cs (tickTraversalSpare tm 2)=firstOutput+count*(configurationWidth tm capacity*(bound+1)) ∧
    cs (.inl 9)+count*tickForestLayerCount tm capacity ≤ layers

theorem TickRetreatIterationBudget.remaining_update (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstInput firstOutput count value : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput count cs)
    (hv : value ≤ wireBound) :
    TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput count
      (Function.update cs (tickTraversalSpare tm 3) value) := by
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h =>
    (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  refine ⟨?_,hs.2.1.update _ value hv,?_,?_,hs.2.2.2.2.1,?_,?_,?_⟩
  · simpa [fixedGuardedEmitterReady,tickTraversalSpare] using hs.1
  · simpa [tickTraversalSpare] using hs.2.2.1
  · unfold TickWindowBudget
    rw [Function.update_of_ne (by simp [tickTraversalSpare]),Function.update_of_ne (by simp [tickTraversalSpare]),Function.update_of_ne h23]
    exact hs.2.2.2.1
  · simpa [tickTraversalSpare] using hs.2.2.2.2.2.1
  · rw [Function.update_of_ne h23]
    exact hs.2.2.2.2.2.2.1
  · simpa [tickTraversalSpare] using hs.2.2.2.2.2.2.2

/-- A real forward-block emission retreats by one whole slice and consumes its reserved layers. -/
theorem tickRetreatIterationBudget_next (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstInput firstOutput k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput (k+1) cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput k
      ((tickRetreatStepTemplate tm (bound+1) bound).counters (Function.update cs (tickTraversalSpare tm 3) k)) := by
  let initial := Function.update cs (tickTraversalSpare tm 3) k
  have ht : TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput (k+1) initial :=
    TickRetreatIterationBudget.remaining_update tm bound wireBound capacity layers firstInput firstOutput (k+1) k cs hs
      (by have hk := hs.2.2.2.2.1; omega)
  have hpos : 0 < initial (.inl 1) := by rw [ht.2.2.1]; exact hc
  have hcap := tickRetreatStepTemplate_control_frame tm (bound+1) bound initial 1 (by decide) (by decide) (by decide)
  refine ⟨tickRetreatStepTemplate_ready_preserved tm (bound+1) bound initial ht.1,
    tickRetreatStepTemplate_static_budget tm (bound+1) bound wireBound initial ht.1 ht.2.1 ht.2.2.2.1 hpos hsize,
    hcap.trans ht.2.2.1,tickRetreatStepTemplate_windows tm (bound+1) bound wireBound initial ht.2.2.2.1,?_,?_,?_,?_⟩
  · have hk := ht.2.2.2.2.1; omega
  · rw [tickRetreatStepTemplate_input]
    change initial (.inl 0)-configurationWidth tm (initial (.inl 1))*(bound+1)=_
    rw [ht.2.2.1,ht.2.2.2.2.2.1]
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  · rw [tickRetreatStepTemplate_output]
    change initial (tickTraversalSpare tm 2)-configurationWidth tm (initial (.inl 1))*(bound+1)=_
    rw [ht.2.2.1,ht.2.2.2.2.2.2.1]
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  · rw [tickRetreatStepTemplate_count]
    change initial (.inl 9)+tickForestLayerCount tm (initial (.inl 1))+k*tickForestLayerCount tm capacity ≤ layers
    rw [ht.2.2.1]
    have hl := ht.2.2.2.2.2.2.2
    simp only [Nat.add_mul,Nat.one_mul] at hl
    omega

end ShiReversibleGenerator
