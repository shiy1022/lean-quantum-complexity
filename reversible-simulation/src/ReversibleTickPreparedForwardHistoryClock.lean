import ReversibleTickPreparedForwardHistoryReady
import ReversibleTickLateWindowClock
import ReversibleTickForwardHistoryClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Polynomial runtime includes the actual count copy, pointer setup and complete forward emission. -/
theorem tickPreparedForwardHistoryTemplate_clock (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n firstOutput (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      fixedGuardedEmitterReady (tickTraversalSupply tm) cs → CounterBudget cs (.inl 9) (budget.eval n) →
      cs (.inl 1)=capacity.eval n → 0 < capacity.eval n → 0 < cs (tickTraversalSpare tm 7) →
      cs (tickTraversalSpare tm 1)=firstOutput+cs (tickTraversalSpare tm 7)*
        (configurationWidth tm (capacity.eval n)*(bound+1)) →
      cs (tickTraversalSpare tm 1)+bound ≤ budget.eval n →
      cs (.inl 9)+(cs (tickTraversalSpare tm 7)-1)*tickForestLayerCount tm (capacity.eval n) ≤ layers.eval n →
      cs (tickTraversalSpare tm 6)+17+18*configurationWidth tm (capacity.eval n) ≤ budget.eval n →
      cs (tickTraversalSpare tm 6)+18*configurationWidth tm (capacity.eval n)+
        configurationWidth tm (capacity.eval n)*(bound+1) ≤ budget.eval n →
      (tickPreparedForwardHistoryTemplate tm bound).steps cs ≤ clock.eval n := by
  obtain ⟨copyClock,hcopy⟩ := tickHistoryCountTemplate_polynomial tm (budget+layers)
  obtain ⟨setupClock,hsetup⟩ := tickLateWindowTemplate_polynomial tm bound (budget+layers)
  obtain ⟨forwardClock,hforward⟩ := tickForwardHistoryTemplate_clock tm bound capacity budget layers hsize
  refine ⟨copyClock+(setupClock+forwardClock),?_⟩
  intro n firstOutput cs hr hb hcap hc ht hend hbound hlayers hin hout
  let initial := (tickHistoryCountTemplate tm).counters cs
  let after := tickPreparedForwardHistoryState tm bound cs
  have hi : initial=Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1) :=
    tickHistoryCountTemplate_counters tm cs
  have hib : CounterBudget initial (.inl 9) (budget.eval n) := by
    rw [hi]; exact hb.update _ _ ((Nat.sub_le _ _).trans (hb _ (by simp [tickTraversalSpare])))
  have hi9 : initial (.inl 9)=cs (.inl 9) := by rw [hi]; simp [tickTraversalSpare]
  have hcount : cs (.inl 9) ≤ layers.eval n := by omega
  have hall : ∀ q,cs q ≤ (budget+layers).eval n := by
    intro q
    rw [Polynomial.eval_add]
    by_cases hq : q=Sum.inl 9
    · subst q; exact hcount.trans (Nat.le_add_left _ _)
    · exact (hb q hq).trans (Nat.le_add_right _ _)
  have hiall : ∀ q,initial q ≤ (budget+layers).eval n := by
    intro q
    rw [Polynomial.eval_add]
    by_cases hq : q=Sum.inl 9
    · subst q; rw [hi9]; exact hcount.trans (Nat.le_add_left _ _)
    · exact (hib q hq).trans (Nat.le_add_right _ _)
  have hready := tickPreparedForwardHistoryTemplate_ready tm bound (budget.eval n) (capacity.eval n)
    (layers.eval n) firstOutput cs hr hb hcap hc hsize ht hend hbound hlayers hin hout
  have hs := tickPreparedForwardHistoryState_budget tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstOutput cs hr hb hcap ht hend hbound hlayers
  have hraw : after (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) :=
    tickPreparedForwardHistoryState_raw_length tm bound cs
  have hcp := hcopy n cs hall hready.1
  have hsp := hsetup n initial hiall hready.2.1
  have hfp := hforward n firstOutput after hs hc (by rw [hraw]; exact hin) (by rw [hraw]; exact hout)
  change (tickHistoryCountTemplate tm).steps cs+((tickLateWindowTemplate tm bound).steps initial+
    (tickForwardHistoryTemplate tm bound).steps after) ≤ _
  simpa only [Polynomial.eval_add] using Nat.add_le_add hcp (Nat.add_le_add hsp hfp)

end ShiReversibleGenerator
