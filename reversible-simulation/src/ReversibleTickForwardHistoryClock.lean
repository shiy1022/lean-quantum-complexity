import ReversibleTickForwardHistoryReady
import ReversibleTickInitializedWindowClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- A polynomial clock covers regular ticks, runtime boundary reset and the initialized tick. -/
theorem tickForwardHistoryTemplate_clock (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n firstOutput (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      TickRetreatHistoryBudget tm bound (budget.eval n) (capacity.eval n) (layers.eval n) firstOutput
        (cs (tickTraversalSpare tm 3)) cs → 0 < capacity.eval n →
      cs (tickTraversalSpare tm 6)+17+18*configurationWidth tm (capacity.eval n) ≤ budget.eval n →
      cs (tickTraversalSpare tm 6)+18*configurationWidth tm (capacity.eval n)+
        configurationWidth tm (capacity.eval n)*(bound+1) ≤ budget.eval n →
      (tickForwardHistoryTemplate tm bound).steps cs ≤ clock.eval n := by
  obtain ⟨loopClock,hloop⟩ := tickRetreatHistoryTemplate_clock tm bound capacity budget layers hsize
  obtain ⟨resetClock,hreset⟩ := tickInitializedWindowTemplate_polynomial tm (budget+layers)
  obtain ⟨boundaryClock,hboundary⟩ := tickForestTemplate_clock tm 18 bound false capacity budget layers hsize
  refine ⟨loopClock+(resetClock+boundaryClock),?_⟩
  intro n firstOutput cs hs hc hin hout
  let after := (tickRetreatIterationTemplate tm bound).counters cs
  let initial := (tickInitializedWindowTemplate tm).counters after
  have hf := tickRetreatHistoryTemplate_final_budget tm bound (budget.eval n) (capacity.eval n) (layers.eval n) firstOutput cs hs hc hsize
  have ha1 : after (.inl 1)=(capacity.eval n) := hf.2.2.1
  have ha6 : after (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) :=
    tickRetreatIterationTemplate_spare_frame tm bound cs 6 (by decide) (by decide) (by decide) (by decide)
  have hb : CounterBudget initial (.inl 9) (budget.eval n) := by
    apply tickInitializedWindowTemplate_static_budget tm (budget.eval n) after hf.2.1
    · rw [ha6]; omega
    · rw [ha6,ha1]; omega
  have hr : fixedGuardedEmitterReady (tickTraversalSupply tm) initial :=
    tickInitializedWindowTemplate_ready_preserved tm after hf.1
  have hi1 : initial (.inl 1)=(capacity.eval n) :=
    (tickInitializedWindowTemplate_control_frame tm after 1 (by decide)).trans ha1
  have hw : TickWindowBudget tm 18 bound (budget.eval n) initial := by
    unfold TickWindowBudget
    dsimp only [initial]
    rw [tickInitializedWindowTemplate_input,tickInitializedWindowTemplate_output,
      tickInitializedWindowTemplate_control_frame tm after 1 (by decide),ha1,ha6]
    exact ⟨hin,hout⟩
  have hcount : after (.inl 9) ≤ layers.eval n := by
    have h := hf.2.2.2.2.2.2.2
    simpa only [Nat.zero_mul,Nat.add_zero] using h
  have hall : ∀ q,after q ≤ (budget+layers).eval n := by
    intro q
    rw [Polynomial.eval_add]
    by_cases hq : q=Sum.inl 9
    · subst q; exact hcount.trans (Nat.le_add_left _ _)
    · exact (hf.2.1 q hq).trans (Nat.le_add_right _ _)
  have hready : (tickInitializedWindowTemplate tm).ready after :=
    (tickInitializedWindowTemplate_ready tm after).2 hf.1.2.2.1
  have hlc := hloop n firstOutput cs hs hc
  have hrc := hreset n after hall hready
  have hbc := hboundary n initial hi1 hr hb hw (by rw [hi1]; exact hc) (by
    dsimp only [initial]
    rw [tickInitializedWindowTemplate_control_frame tm after 9 (by decide)]
    exact hcount)
  change (tickRetreatIterationTemplate tm bound).steps cs+((tickInitializedWindowTemplate tm).steps after+
    (tickForestTemplate tm 18 bound false).steps initial) ≤ _
  simpa only [Polynomial.eval_add] using Nat.add_le_add hlc (Nat.add_le_add hrc hbc)

end ShiReversibleGenerator
