import ReversibleTickForwardHistoryTemplate
import ReversibleTickInitializedWindowBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Concrete initialized boundary bounds suffice after the clamped regular loop. -/
theorem tickForwardHistoryTemplate_ready (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    (hin : cs (tickTraversalSpare tm 6)+17+18*configurationWidth tm capacity ≤ wireBound)
    (hout : cs (tickTraversalSpare tm 6)+18*configurationWidth tm capacity+
      configurationWidth tm capacity*(bound+1) ≤ wireBound) :
    (tickForwardHistoryTemplate tm bound).ready cs := by
  let after := (tickRetreatIterationTemplate tm bound).counters cs
  let initial := (tickInitializedWindowTemplate tm).counters after
  have hf := tickRetreatHistoryTemplate_final_budget tm bound wireBound capacity layers firstOutput cs hs hc hsize
  have ha1 : after (.inl 1)=capacity := hf.2.2.1
  have ha6 : after (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) :=
    tickRetreatIterationTemplate_spare_frame tm bound cs 6 (by decide) (by decide) (by decide) (by decide)
  have hb : CounterBudget initial (.inl 9) wireBound := by
    apply tickInitializedWindowTemplate_static_budget tm wireBound after hf.2.1
    · rw [ha6]; omega
    · rw [ha6,ha1]; omega
  have hr : fixedGuardedEmitterReady (tickTraversalSupply tm) initial :=
    tickInitializedWindowTemplate_ready_preserved tm after hf.1
  have hi1 : initial (.inl 1)=capacity :=
    (tickInitializedWindowTemplate_control_frame tm after 1 (by decide)).trans ha1
  have hw : TickWindowBudget tm 18 bound wireBound initial := by
    unfold TickWindowBudget
    dsimp only [initial]
    rw [tickInitializedWindowTemplate_input,tickInitializedWindowTemplate_output,
      tickInitializedWindowTemplate_control_frame tm after 1 (by decide),ha1,ha6]
    exact ⟨hin,hout⟩
  change (tickRetreatIterationTemplate tm bound).ready cs ∧
    (tickInitializedWindowTemplate tm).ready after ∧ (tickForestTemplate tm 18 bound false).ready initial
  refine ⟨tickRetreatHistoryTemplate_ready tm bound wireBound capacity layers firstOutput cs hs hc hsize,?_,?_⟩
  · rw [tickInitializedWindowTemplate_ready]
    exact hf.1.2.2.1
  · exact (tickForestTemplate_ready_and_budget tm 18 bound false wireBound initial hr hb hw
      (by rw [hi1]; exact hc) hsize).1

end ShiReversibleGenerator
