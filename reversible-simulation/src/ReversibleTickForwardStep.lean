import ReversibleTickWindowAdvance
import ReversibleTickForestLayerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickForwardStepTemplate (tm : Turing.FinTM2) (inputStride bound : Nat) :=
  sequenceProgramTemplate (tickForestTemplate tm inputStride bound false) (tickWindowAdvanceTemplate tm bound)

theorem tickForwardStepTemplate_embeds (tm : Turing.FinTM2) (inputStride bound : Nat) :
    (tickForwardStepTemplate tm inputStride bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickForestTemplate_embeds tm inputStride bound false)
    (tickWindowAdvanceTemplate_embeds tm bound)

theorem tickForwardStepTemplate_run (tm : Turing.FinTM2) (inputStride bound : Nat) :
    (tickForwardStepTemplate tm inputStride bound).Runs :=
  sequenceProgramTemplate_run _ _ (tickForestTemplate_embeds tm inputStride bound false)
    (tickForestTemplate_run tm inputStride bound false) (tickWindowAdvanceTemplate_run tm bound)

theorem tickForwardStepTemplate_ready (tm : Turing.FinTM2) (inputStride bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride bound wireBound cs)
    (hc : 0 < cs (.inl 1)) (hsize : tickSizeBound tm ≤ bound) :
    (tickForwardStepTemplate tm inputStride bound).ready cs := by
  have hs := tickForestTemplate_ready_and_budget tm inputStride bound false wireBound cs hr hb hw hc hsize
  exact ⟨hs.1,(tickWindowAdvanceTemplate_ready tm bound _).mpr hs.2.2.2.2.2.1⟩

theorem tickForwardStepTemplate_input (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardStepTemplate tm inputStride bound).counters cs (.inl 0)=cs (tickTraversalSpare tm 2)+bound := by
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (.inl 0)=_
  rw [tickWindowAdvanceTemplate_counters]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 2),Function.update_self]
  rw [tickForestTemplate_spare_frame tm inputStride bound false cs 2 (by decide)]

theorem tickForwardStepTemplate_output (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardStepTemplate tm inputStride bound).counters cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 2)+configurationWidth tm (cs (.inl 1))*(bound+1) := by
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (tickTraversalSpare tm 2)=_
  rw [tickWindowAdvanceTemplate_counters,Function.update_self,
    tickForestTemplate_spare_frame tm inputStride bound false cs 2 (by decide),
    tickForestTemplate_control_frame tm inputStride bound false cs 1 (by decide) (by decide)]

theorem tickForwardStepTemplate_count (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardStepTemplate tm inputStride bound).counters cs (.inl 9)=cs (.inl 9)+tickForestLayerCount tm (cs (.inl 1)) := by
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (.inl 9)=_
  rw [tickWindowAdvanceTemplate_counters]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 2),
    Function.update_of_ne (by simp : (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 0)]
  exact tickForestTemplate_count tm inputStride bound false cs

theorem tickForwardStepTemplate_bytes (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickForwardStepTemplate tm inputStride bound).bytes cs=(tickForestTemplate tm inputStride bound false).bytes cs := rfl

end ShiReversibleGenerator
