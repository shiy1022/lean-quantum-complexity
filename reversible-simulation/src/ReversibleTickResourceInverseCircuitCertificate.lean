import ReversibleTickResourceInverseHypotheses
import ReversibleTickFullInverseHistoryCircuitCertificate

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The initialized real prelude instantiates all budgets of the complete inverse history circuit printer. -/
theorem tickResourceInverse_circuit_certificate (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r) →
      (∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) → 0 < time.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (ys : List Bool) (wires : Nat)
        (hout : n+18*configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)+
          time.eval n*(configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)*(tickSizeBound tm+1)) ≤ wires),
      let cap := (tickRuntimeCapacityPolynomial tm time).eval n
      let firstOutput := n+18*configurationWidth tm cap
          let start := tickResourceInverseStart tm cs
      let p := tickInverseHistoryTemplate tm (tickSizeBound tm)
      let hin : ∀ i : Fin (configurationWidth tm cap),n+17+18*i.val < firstOutput := by
        intro i
        have hi := i.isLt
        omega
      let gs := tickStridedHistoryQuantumLayers tm cap (n+17) 18 firstOutput (tickSizeBound tm)
        (time.eval n) wires (Nat.le_refl _) hin hout true
      CounterRun (p.code caller stop) ⟨some (p.entry stop),start,ys⟩ (p.steps start)
        ⟨some (p.exit stop),p.counters start,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps start ≤ clock.eval n ∧ p.counters start (.inl 9)=gs.length ∧
      p.counters start (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickInverseHistoryTemplate_circuit_certificate tm (tickSizeBound tm)
    (tickRuntimeCapacityPolynomial tm time) (tickInverseRuntimeBudgetPolynomial tm time)
    (tickRuntimeHistoryLayerPolynomial tm time) (Nat.le_refl _)
  refine ⟨clock,?_⟩
  intro n cs hpull houtside ht L caller stop ys wires hout
  dsimp only
  let start := tickResourceInverseStart tm cs
  obtain ⟨hr,hb,hw,hcap,hc,htime,hlayers,hfuture,hinput,houtput,hT,hzero⟩ :=
    tickResourceInverseStart_hypotheses tm time n cs hpull houtside ht
  have hin : ∀ i : Fin (configurationWidth tm ((tickResourceInverseStart tm cs) (.inl 1))),
      (tickResourceInverseStart tm cs) (.inl 0)+18*i.val < (tickResourceInverseStart tm cs) (tickTraversalSpare tm 2) := by
    rw [hinput,houtput,hcap]
    intro i
    have hi := i.isLt
    omega
  have hout' : (tickResourceInverseStart tm cs) (tickTraversalSpare tm 2)+(tickResourceInverseStart tm cs) (tickTraversalSpare tm 7)*
      (configurationWidth tm ((tickResourceInverseStart tm cs) (.inl 1))*(tickSizeBound tm+1)) ≤ wires := by
    simpa only [houtput,hT,hcap] using hout
  have hcert := hclock n (tickResourceInverseStart tm cs) ys hr hb hw hcap hc htime hlayers hfuture L caller stop wires hin hout'
  simpa only [hcap,hinput,houtput,hT,hzero,Nat.zero_add] using hcert

end ShiReversibleGenerator
