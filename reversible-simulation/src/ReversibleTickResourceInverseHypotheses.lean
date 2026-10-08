import ReversibleTickResourceHistoryHypotheses
import ReversibleTickRuntimePolynomials
import ReversibleTickInitializedWindowBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The advancing inverse printer needs one extra virtual window beyond the last physical history slice. -/
noncomputable def tickInverseRuntimeBudgetPolynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :=
  tickRuntimeHistoryBudgetPolynomial tm time+
    tickRuntimeWidthPolynomial tm time*Polynomial.C (tickSizeBound tm+1)

noncomputable def tickResourceInverseStart (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :=
  (tickInitializedWindowTemplate tm).counters ((tickMetadataHandoffTemplate tm).counters cs)

/-- Actual prelude metadata and initialized-window setup supply every inverse-history runtime hypothesis. -/
theorem tickResourceInverseStart_hypotheses (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hpull : ∀ r,cs (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r)
    (houtside : ∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) (ht : 0 < time.eval n) :
    let cap := (tickRuntimeCapacityPolynomial tm time).eval n
    let budget := (tickInverseRuntimeBudgetPolynomial tm time).eval n
    let layers := (tickRuntimeHistoryLayerPolynomial tm time).eval n
    let final := tickResourceInverseStart tm cs
    fixedGuardedEmitterReady (tickTraversalSupply tm) final ∧ CounterBudget final (.inl 9) budget ∧
      TickWindowBudget tm 18 (tickSizeBound tm) budget final ∧
      final (.inl 1)=cap ∧ 0 < cap ∧ 0 < final (tickTraversalSpare tm 7) ∧
      final (.inl 9)+final (tickTraversalSpare tm 7)*tickForestLayerCount tm cap ≤ layers ∧
      final (tickTraversalSpare tm 2)+(final (tickTraversalSpare tm 7)+1)*
        (configurationWidth tm cap*(tickSizeBound tm+1)) ≤ budget ∧
      final (.inl 0)=n+17 ∧ final (tickTraversalSpare tm 2)=n+18*configurationWidth tm cap ∧
      final (tickTraversalSpare tm 7)=time.eval n ∧ final (.inl 9)=0 := by
  dsimp only
  let hand := (tickMetadataHandoffTemplate tm).counters cs
  obtain ⟨hr,hb,hcap,hc,htime,hend,he,hl,hi,ho,hfirst⟩ :=
    tickResourceHandoff_history_hypotheses tm time n cs hpull houtside ht
  obtain ⟨_,hraw,hT,_,_,_,h9⟩ := tickResourcePrelude_handoff_result tm n (time.eval n) cs hpull
  have hcap' : hand (.inl 1)=(tickRuntimeCapacityPolynomial tm time).eval n := by
    simpa only [tickRuntimeCapacityPolynomial_eval,hand] using hcap
  have hb' : CounterBudget hand (.inl 9) ((tickRuntimeHistoryBudgetPolynomial tm time).eval n) := by
    simpa only [tickRuntimeHistoryBudgetPolynomial_eval,hand] using hb
  have hB : (tickRuntimeHistoryBudgetPolynomial tm time).eval n ≤
      (tickInverseRuntimeBudgetPolynomial tm time).eval n := by
    simp only [tickInverseRuntimeBudgetPolynomial,Polynomial.eval_add]
    exact Nat.le_add_right _ _
  have hin : hand (tickTraversalSpare tm 6)+17 ≤ (tickInverseRuntimeBudgetPolynomial tm time).eval n := by
    have hi' : hand (tickTraversalSpare tm 6)+17+18*configurationWidth tm (hand (.inl 1)) ≤
        (tickRuntimeHistoryBudgetPolynomial tm time).eval n := by
      simpa only [hand,tickRuntimeHistoryBudgetPolynomial_eval,hcap] using hi
    omega
  have hout : hand (tickTraversalSpare tm 6)+18*configurationWidth tm (hand (.inl 1)) ≤
      (tickInverseRuntimeBudgetPolynomial tm time).eval n := by
    have ho' : hand (tickTraversalSpare tm 6)+18*configurationWidth tm (hand (.inl 1))+
        configurationWidth tm (hand (.inl 1))*(tickSizeBound tm+1) ≤
        (tickRuntimeHistoryBudgetPolynomial tm time).eval n := by
      simpa only [hand,tickRuntimeHistoryBudgetPolynomial_eval,hcap] using ho
    omega
  have hstatic : CounterBudget (tickResourceInverseStart tm cs) (.inl 9)
      ((tickInverseRuntimeBudgetPolynomial tm time).eval n) := by
    apply tickInitializedWindowTemplate_static_budget tm _ hand
    · intro q hq
      exact (hb' q hq).trans hB
    · exact hin
    · exact hout
  have hinput : tickResourceInverseStart tm cs (.inl 0)=n+17 := by
    simpa only [tickResourceInverseStart,hand,hraw] using tickInitializedWindowTemplate_input tm hand
  have houtput : tickResourceInverseStart tm cs (tickTraversalSpare tm 2)=
      n+18*configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n) := by
    simpa only [tickResourceInverseStart,hand,hraw,hcap,tickRuntimeCapacityPolynomial_eval] using tickInitializedWindowTemplate_output tm hand
  have hcapacity : tickResourceInverseStart tm cs (.inl 1)=(tickRuntimeCapacityPolynomial tm time).eval n := by
    simpa only [tickResourceInverseStart,hand,hcap,tickRuntimeCapacityPolynomial_eval] using tickInitializedWindowTemplate_control_frame tm hand 1 (by decide)
  have hcount : tickResourceInverseStart tm cs (.inl 9)=0 := by
    simpa only [tickResourceInverseStart,hand,h9] using tickInitializedWindowTemplate_control_frame tm hand 9 (by decide)
  have htimeframe : (tickResourceInverseStart tm cs) (tickTraversalSpare tm 7)=time.eval n := by
    rw [tickResourceInverseStart,tickInitializedWindowTemplate_counters]
    simpa [tickTraversalSpare] using hT
  refine ⟨tickInitializedWindowTemplate_ready_preserved tm hand hr,hstatic,?_,hcapacity,?_,?_,?_,?_,?_,?_,htimeframe,?_⟩
  · unfold TickWindowBudget
    rw [hinput,houtput,hcapacity]
    constructor
    · have hi' := hi
      rw [hraw] at hi'
      rw [tickRuntimeCapacityPolynomial_eval]
      simp only [tickInverseRuntimeBudgetPolynomial,Polynomial.eval_add,tickRuntimeHistoryBudgetPolynomial_eval]
      omega
    · have ho' := ho
      rw [hraw] at ho'
      rw [tickRuntimeCapacityPolynomial_eval]
      simp only [tickInverseRuntimeBudgetPolynomial,Polynomial.eval_add,tickRuntimeHistoryBudgetPolynomial_eval]
      omega
  · simpa only [tickRuntimeCapacityPolynomial_eval] using hc
  · rw [htimeframe]; exact ht
  · rw [hcount,htimeframe,Nat.zero_add,tickRuntimeHistoryLayerPolynomial_eval,tickRuntimeCapacityPolynomial_eval]
    calc
      time.eval n*tickForestLayerCount tm (n+time.eval n*machinePushBound tm+1) ≤
          time.eval n*(configurationWidth tm (n+time.eval n*machinePushBound tm+1)*(37*tickSizeBound tm+1)) :=
        Nat.mul_le_mul_left _ (tickForestLayerCount_bound tm _ hc)
      _ = _ := by ring
  · rw [houtput,htimeframe]
    have he' := he
    rw [hend,hT] at he'
    simp only [tickInverseRuntimeBudgetPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      tickRuntimeWidthPolynomial_eval,tickRuntimeCapacityPolynomial_eval,tickRuntimeHistoryBudgetPolynomial_eval]
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  · exact hinput
  · exact houtput
  · exact hcount

end ShiReversibleGenerator
