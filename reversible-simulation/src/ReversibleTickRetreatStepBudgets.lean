import ReversibleTickRetreatStepCounters
import ReversibleTickRetreatStepClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Both retreat pointers only decrease, and its private width counter is cleared. -/
theorem tickRetreatStepTemplate_static_budget (tm : Turing.FinTM2) (inputStride bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride bound wireBound cs)
    (hc : 0 < cs (.inl 1)) (hsize : tickSizeBound tm ≤ bound) :
    CounterBudget ((tickRetreatStepTemplate tm inputStride bound).counters cs) (.inl 9) wireBound := by
  let after := (tickForestTemplate tm inputStride bound false).counters cs
  have hs := tickForestTemplate_ready_and_budget tm inputStride bound false wireBound cs hr hb hw hc hsize
  have hi : after (.inl 0)-configurationWidth tm (after (.inl 1))*(bound+1) ≤ wireBound :=
    (Nat.sub_le _ _).trans (hs.2.1 (.inl 0) (by simp))
  have ho : after (tickTraversalSpare tm 2)-configurationWidth tm (after (.inl 1))*(bound+1) ≤ wireBound :=
    (Nat.sub_le _ _).trans (hs.2.1 _ (by simp [tickTraversalSpare]))
  change CounterBudget ((tickWindowRetreatTemplate tm bound).counters after) (.inl 9) wireBound
  rw [tickWindowRetreatTemplate_counters]
  exact ((hs.2.1.update (.inl 0) _ hi).update (tickTraversalSpare tm 2) _ ho).update (tickTraversalSpare tm 4) 0 (Nat.zero_le _)

/-- Decreasing both pointers preserves the two window upper bounds. -/
theorem tickRetreatStepTemplate_windows (tm : Turing.FinTM2) (inputStride bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hw : TickWindowBudget tm inputStride bound wireBound cs) :
    TickWindowBudget tm inputStride bound wireBound ((tickRetreatStepTemplate tm inputStride bound).counters cs) := by
  unfold TickWindowBudget
  rw [tickRetreatStepTemplate_input,tickRetreatStepTemplate_output,
    tickRetreatStepTemplate_control_frame tm inputStride bound cs 1 (by decide) (by decide) (by decide)]
  exact ⟨(Nat.add_le_add_right (Nat.sub_le _ _) _).trans hw.1,
    (Nat.add_le_add_right (Nat.sub_le _ _) _).trans hw.2⟩

end ShiReversibleGenerator
