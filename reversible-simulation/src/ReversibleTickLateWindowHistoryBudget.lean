import ReversibleTickLateWindowBudget
import ReversibleTickRetreatHistoryBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- A positive runtime history length gives the actual clamped forward-loop starting invariant. -/
theorem tickLateWindowTemplate_history_budget (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput t : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hcap : cs (.inl 1)=capacity)
    (ht : 0 < t) (hcount : t-1 ≤ wireBound)
    (hend : cs (tickTraversalSpare tm 1)=firstOutput+t*(configurationWidth tm capacity*(bound+1)))
    (hbound : cs (tickTraversalSpare tm 1)+bound ≤ wireBound)
    (hlayers : cs (.inl 9)+(t-1)*tickForestLayerCount tm capacity ≤ layers) :
    TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput (t-1)
      ((tickLateWindowTemplate tm bound).counters cs) := by
  let after := (tickLateWindowTemplate tm bound).counters cs
  let width := configurationWidth tm capacity*(bound+1)
  have ht' : t-1+1=t := Nat.sub_add_cancel (Nat.succ_le_of_lt ht)
  have he : cs (tickTraversalSpare tm 1)=firstOutput+(t-1)*width+width := by
    rw [hend,←ht']
    simp only [width,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_sub_cancel]
  have hi : after (.inl 0)=(firstOutput+(t-1)*width+bound)-width := by
    dsimp only [after]
    rw [tickLateWindowTemplate_input,hcap,he]
    change (firstOutput+(t-1)*width+width+bound)-2*width=(firstOutput+(t-1)*width+bound)-width
    omega
  have ho : after (tickTraversalSpare tm 2)=firstOutput+(t-1)*width := by
    dsimp only [after]
    rw [tickLateWindowTemplate_output,hcap,he]
    change (firstOutput+(t-1)*width+width)-width=firstOutput+(t-1)*width
    omega
  have hc : after (.inl 1)=capacity :=
    (tickLateWindowTemplate_control_frame tm bound cs 1 (by decide)).trans hcap
  refine ⟨tickLateWindowTemplate_ready_preserved tm bound cs hr,
    tickLateWindowTemplate_static_budget tm bound wireBound cs hb hbound,hc,?_,hcount,hi,ho,?_⟩
  · unfold TickWindowBudget
    change after (.inl 0)+(bound+1)*configurationWidth tm (after (.inl 1)) ≤ wireBound ∧
      after (tickTraversalSpare tm 2)+configurationWidth tm (after (.inl 1))*(bound+1) ≤ wireBound
    rw [hi,ho,hc,Nat.mul_comm (bound+1) (configurationWidth tm capacity)]
    change (firstOutput+(t-1)*width+bound)-width+width ≤ wireBound ∧
      firstOutput+(t-1)*width+width ≤ wireBound
    rw [he] at hbound
    omega
  · rw [tickLateWindowTemplate_control_frame tm bound cs 9 (by decide)]
    exact hlayers

end ShiReversibleGenerator
