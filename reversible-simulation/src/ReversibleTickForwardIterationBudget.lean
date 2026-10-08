import ReversibleTickForwardStepBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

def TickForwardIterationBudget (tm : Turing.FinTM2) (bound wireBound capacity count : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) : Prop :=
  fixedGuardedEmitterReady (tickTraversalSupply tm) cs ∧ CounterBudget cs (.inl 9) wireBound ∧ cs (.inl 1)=capacity ∧
    TickWindowBudget tm (bound+1) bound wireBound cs ∧ count ≤ wireBound ∧
    cs (tickTraversalSpare tm 2)+(count+1)*(configurationWidth tm capacity*(bound+1)) ≤ wireBound

theorem TickForwardIterationBudget.remaining_update (tm : Turing.FinTM2) (bound wireBound capacity count value : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hs : TickForwardIterationBudget tm bound wireBound capacity count cs)
    (hv : value ≤ wireBound) :
    TickForwardIterationBudget tm bound wireBound capacity count (Function.update cs (tickTraversalSpare tm 3) value) := by
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h => (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  refine ⟨?_,hs.2.1.update _ value hv,?_,?_,hs.2.2.2.2.1,?_⟩
  · simpa [fixedGuardedEmitterReady,tickTraversalSpare] using hs.1
  · simpa [tickTraversalSpare] using hs.2.2.1
  · unfold TickWindowBudget
    rw [Function.update_of_ne (by simp [tickTraversalSpare]),Function.update_of_ne (by simp [tickTraversalSpare]),Function.update_of_ne h23]
    exact hs.2.2.2.1
  · rw [Function.update_of_ne h23]
    exact hs.2.2.2.2.2

/-- Remaining-tick allowance is consumed by exactly one actual emission-and-advance step. -/
theorem tickForwardIterationBudget_next (tm : Turing.FinTM2) (bound wireBound capacity k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickForwardIterationBudget tm bound wireBound capacity (k+1) cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    TickForwardIterationBudget tm bound wireBound capacity k
      ((tickForwardStepTemplate tm (bound+1) bound).counters (Function.update cs (tickTraversalSpare tm 3) k)) := by
  let initial := Function.update cs (tickTraversalSpare tm 3) k
  have ht : TickForwardIterationBudget tm bound wireBound capacity (k+1) initial := TickForwardIterationBudget.remaining_update tm bound wireBound capacity (k+1) k cs hs (by have hk := hs.2.2.2.2.1; omega)
  have hpos : 0 < initial (.inl 1) := by rw [ht.2.2.1]; exact hc
  have hcap := tickForwardStepTemplate_control_frame tm (bound+1) bound initial 1 (by decide) (by decide) (by decide)
  have hallow : initial (tickTraversalSpare tm 2)+2*(configurationWidth tm (initial (.inl 1))*(bound+1)) ≤ wireBound := by
    have hf := ht.2.2.2.2.2
    rw [ht.2.2.1]
    have hm := Nat.mul_le_mul_right (configurationWidth tm capacity*(bound+1)) (by omega : 2 ≤ k+1+1)
    omega
  refine ⟨tickForwardStepTemplate_ready_preserved tm (bound+1) bound initial ht.1,
    tickForwardStepTemplate_static_budget tm (bound+1) bound wireBound initial ht.1 ht.2.1 ht.2.2.2.1 hpos hsize,
    hcap.trans ht.2.2.1,tickForwardStepTemplate_windows tm bound wireBound initial hallow,?_,?_⟩
  · have hk := ht.2.2.2.2.1; omega
  · rw [tickForwardStepTemplate_output]
    change initial (tickTraversalSpare tm 2)+configurationWidth tm (initial (.inl 1))*(bound+1)+
      (k+1)*(configurationWidth tm capacity*(bound+1)) ≤ wireBound
    rw [ht.2.2.1]
    have hf := ht.2.2.2.2.2
    simp only [Nat.add_mul,Nat.one_mul] at hf ⊢
    omega

end ShiReversibleGenerator
