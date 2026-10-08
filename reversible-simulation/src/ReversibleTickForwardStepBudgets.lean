import ReversibleTickForwardStepFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem tickConfigurationWidth_positive (tm : Turing.FinTM2) (capacity : Nat) : 0 < configurationWidth tm capacity := by
  have h : 0 < Fintype.card (Option tm.Λ) := Fintype.card_pos_iff.mpr ⟨none⟩
  simp only [configurationWidth]
  omega

theorem tickStride_dominates_padding (tm : Turing.FinTM2) (capacity bound : Nat) :
    bound ≤ configurationWidth tm capacity*(bound+1) := by
  have h := Nat.mul_le_mul_right (bound+1) (Nat.succ_le_of_lt (tickConfigurationWidth_positive tm capacity))
  simp only [Nat.one_mul] at h
  omega

/-- The advance's new input and output addresses remain within the same static counter budget. -/
theorem tickForwardStepTemplate_static_budget (tm : Turing.FinTM2) (inputStride bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride bound wireBound cs)
    (hc : 0 < cs (.inl 1)) (hsize : tickSizeBound tm ≤ bound) :
    CounterBudget ((tickForwardStepTemplate tm inputStride bound).counters cs) (.inl 9) wireBound := by
  let after := (tickForestTemplate tm inputStride bound false).counters cs
  have hs := tickForestTemplate_ready_and_budget tm inputStride bound false wireBound cs hr hb hw hc hsize
  have ho : after (tickTraversalSpare tm 2)+configurationWidth tm (after (.inl 1))*(bound+1) ≤ wireBound := hs.2.2.1.2
  have hd := tickStride_dominates_padding tm (after (.inl 1)) bound
  have hi : after (tickTraversalSpare tm 2)+bound ≤ wireBound := by omega
  change CounterBudget ((tickWindowAdvanceTemplate tm bound).counters after) (.inl 9) wireBound
  rw [tickWindowAdvanceTemplate_counters]
  exact (hs.2.1.update (.inl 0) _ hi).update (tickTraversalSpare tm 2) _ ho

/-- One additional output-window allowance also covers the next strided input window. -/
theorem tickForwardStepTemplate_windows (tm : Turing.FinTM2) (bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hfuture : cs (tickTraversalSpare tm 2)+2*(configurationWidth tm (cs (.inl 1))*(bound+1)) ≤ wireBound) :
    TickWindowBudget tm (bound+1) bound wireBound ((tickForwardStepTemplate tm (bound+1) bound).counters cs) := by
  unfold TickWindowBudget
  rw [tickForwardStepTemplate_input,tickForwardStepTemplate_output,
    tickForwardStepTemplate_control_frame tm (bound+1) bound cs 1 (by decide) (by decide) (by decide)]
  have hd := tickStride_dominates_padding tm (cs (.inl 1)) bound
  rw [Nat.mul_comm (bound+1) (configurationWidth tm (cs (.inl 1)))]
  constructor <;> omega

end ShiReversibleGenerator
