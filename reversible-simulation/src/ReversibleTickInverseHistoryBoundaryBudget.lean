import ReversibleTickInverseHistoryTemplate
import ReversibleTickInverseAdvanceIterationLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickInverseHistoryBoundary_windows (tm : Turing.FinTM2) (bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hf : cs (tickTraversalSpare tm 2)+2*(configurationWidth tm (cs (.inl 1))*(bound+1)) ≤ wireBound) :
    TickWindowBudget tm (bound+1) bound wireBound ((tickInverseAdvanceStepTemplate tm 18 bound).counters cs) := by
  unfold TickWindowBudget
  rw [tickInverseAdvanceStepTemplate_input,tickInverseAdvanceStepTemplate_output,
    tickInverseAdvanceStepTemplate_control_frame tm 18 bound cs 1 (by decide) (by decide) (by decide)]
  have hd := tickStride_dominates_padding tm (cs (.inl 1)) bound
  rw [Nat.mul_comm (bound+1) (configurationWidth tm (cs (.inl 1)))]
  constructor <;> omega

/-- The real count copy and initialized boundary tick establish the regular inverse-loop budget. -/
theorem tickInverseHistoryBoundary_budget (tm : Turing.FinTM2) (bound wireBound capacity layers : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm 18 bound wireBound cs)
    (hcap : cs (.inl 1)=capacity) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    (ht : 0 < cs (tickTraversalSpare tm 7))
    (hl : cs (.inl 9)+cs (tickTraversalSpare tm 7)*tickForestLayerCount tm capacity ≤ layers)
    (hf : cs (tickTraversalSpare tm 2)+(cs (tickTraversalSpare tm 7)+1)*
      (configurationWidth tm capacity*(bound+1)) ≤ wireBound) :
    let after := (tickInverseAdvanceStepTemplate tm 18 bound).counters ((tickHistoryCountTemplate tm).counters cs)
    TickForwardIterationLayerBudget tm bound wireBound capacity layers (after (tickTraversalSpare tm 3)) after := by
  rw [tickHistoryCountTemplate_counters]
  let initial := Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1)
  let after := (tickInverseAdvanceStepTemplate tm 18 bound).counters initial
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h =>
    (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  have hn : cs (tickTraversalSpare tm 7)-1+1=cs (tickTraversalSpare tm 7) := Nat.sub_add_cancel (Nat.succ_le_of_lt ht)
  have htb : cs (tickTraversalSpare tm 7) ≤ wireBound := hb _ (by simp [tickTraversalSpare])
  have hir : fixedGuardedEmitterReady (tickTraversalSupply tm) initial := by
    simpa [initial,fixedGuardedEmitterReady,tickTraversalSpare] using hr
  have hib : CounterBudget initial (.inl 9) wireBound := hb.update _ _ ((Nat.sub_le _ _).trans htb)
  have hic : initial (.inl 1)=capacity := by simpa [initial,tickTraversalSpare] using hcap
  have hiw : TickWindowBudget tm 18 bound wireBound initial := by
    simpa [initial,TickWindowBudget,tickTraversalSpare] using hw
  have hiout : initial (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2) := Function.update_of_ne h23 _ _
  have hi9 : initial (.inl 9)=cs (.inl 9) := by simp [initial,tickTraversalSpare]
  have hallow : initial (tickTraversalSpare tm 2)+2*(configurationWidth tm (initial (.inl 1))*(bound+1)) ≤ wireBound := by
    rw [hiout,hic]
    have hm := Nat.mul_le_mul_right (configurationWidth tm capacity*(bound+1)) (by omega : 2 ≤ cs (tickTraversalSpare tm 7)+1)
    omega
  have hrem : after (tickTraversalSpare tm 3)=cs (tickTraversalSpare tm 7)-1 := by
    dsimp only [after]
    rw [tickInverseAdvanceStepTemplate_spare_frame tm 18 bound _ 3 (by decide) (by decide)]
    simp [initial]
  change TickForwardIterationLayerBudget tm bound wireBound capacity layers (after (tickTraversalSpare tm 3)) after
  rw [hrem]
  refine ⟨⟨tickInverseAdvanceStepTemplate_ready_preserved tm 18 bound initial hir,
    tickInverseAdvanceStepTemplate_static_budget tm 18 bound wireBound initial hir hib hiw
      (by rw [hic]; exact hc) hsize,
    (tickInverseAdvanceStepTemplate_control_frame tm 18 bound initial 1 (by decide) (by decide) (by decide)).trans hic,
    tickInverseHistoryBoundary_windows tm bound wireBound initial hallow,
    (Nat.sub_le _ _).trans htb,?_⟩,?_⟩
  · change after (tickTraversalSpare tm 2)+(cs (tickTraversalSpare tm 7)-1+1)*
      (configurationWidth tm capacity*(bound+1)) ≤ wireBound
    dsimp only [after]
    rw [tickInverseAdvanceStepTemplate_output,hiout,hic,hn]
    have h := hf
    simp only [Nat.add_mul,Nat.one_mul] at h
    omega
  · change after (.inl 9)+(cs (tickTraversalSpare tm 7)-1)*tickForestLayerCount tm capacity ≤ layers
    dsimp only [after]
    rw [tickInverseAdvanceStepTemplate_count,hi9,hic]
    have h : cs (.inl 9)+(cs (tickTraversalSpare tm 7)-1+1)*tickForestLayerCount tm capacity ≤ layers := by rw [hn]; exact hl
    simp only [Nat.add_mul,Nat.one_mul] at h
    omega

end ShiReversibleGenerator
