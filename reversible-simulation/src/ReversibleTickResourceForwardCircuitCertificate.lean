import ReversibleTickRuntimePolynomials
import ReversibleTickPreparedForwardHistoryCircuitCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual prelude and metadata handoff instantiate every runtime budget of the full forward circuit printer. -/
theorem tickResourceForward_circuit_certificate (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r) →
      (∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) → 0 < time.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (ys : List Bool) (wires : Nat)
        (hout : n+18*configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)+
          time.eval n*(configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)*(tickSizeBound tm+1)) ≤ wires),
      let cap := (tickRuntimeCapacityPolynomial tm time).eval n
      let firstOutput := n+18*configurationWidth tm cap
      let start := (tickMetadataHandoffTemplate tm).counters cs
      let p := tickPreparedForwardHistoryTemplate tm (tickSizeBound tm)
      let hin : ∀ i : Fin (configurationWidth tm cap),n+17+18*i.val < firstOutput := by
        intro i
        have hi := i.isLt
        omega
      let gs := tickStridedHistoryQuantumLayers tm cap (n+17) 18 firstOutput (tickSizeBound tm)
        (time.eval n) wires (Nat.le_refl _) hin hout false
      CounterRun (p.code caller stop) ⟨some (p.entry stop),start,ys⟩ (p.steps start)
        ⟨some (p.exit stop),p.counters start,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps start ≤ clock.eval n ∧ p.counters start (.inl 9)=gs.length ∧
      p.counters start (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickPreparedForwardHistoryTemplate_circuit_certificate tm (tickSizeBound tm)
    (tickRuntimeCapacityPolynomial tm time) (tickRuntimeHistoryBudgetPolynomial tm time)
    (tickRuntimeHistoryLayerPolynomial tm time) (Nat.le_refl _)
  refine ⟨clock,?_⟩
  intro n cs hpull houtside ht L caller stop ys wires hout
  dsimp only
  let start := (tickMetadataHandoffTemplate tm).counters cs
  have h := tickResourceHandoff_history_hypotheses tm time n cs hpull houtside ht
  dsimp only at h
  obtain ⟨hr,hb,hcap,hc,htime,hend,hbound,hlayers,hi,ho,hfirst⟩ := h
  have hraw : start (tickTraversalSpare tm 6)=n :=
    (tickResourcePrelude_handoff_result tm n (time.eval n) cs hpull).2.1
  have htime' : start (tickTraversalSpare tm 7)=time.eval n :=
    (tickResourcePrelude_handoff_result tm n (time.eval n) cs hpull).2.2.1
  have hzero : start (.inl 9)=0 := (tickMetadataHandoffTemplate_metadata tm cs).2.2.2.2.2
  have hin : ∀ i : Fin (configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)),
      n+17+18*i.val < n+18*configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n) := by
    intro i
    have hi := i.isLt
    omega
  have hcert := hclock n (n+18*configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)) start ys hr
    (by simpa only [tickRuntimeHistoryBudgetPolynomial_eval] using hb)
    (by simpa only [tickRuntimeCapacityPolynomial_eval] using hcap)
    (by simpa only [tickRuntimeCapacityPolynomial_eval] using hc) htime
    (by simpa only [tickRuntimeCapacityPolynomial_eval] using hend)
    (by simpa only [tickRuntimeHistoryBudgetPolynomial_eval] using hbound)
    (by simpa only [tickRuntimeCapacityPolynomial_eval,tickRuntimeHistoryLayerPolynomial_eval] using hlayers)
    (by simpa only [tickRuntimeCapacityPolynomial_eval,tickRuntimeHistoryBudgetPolynomial_eval] using hi)
    (by simpa only [tickRuntimeCapacityPolynomial_eval,tickRuntimeHistoryBudgetPolynomial_eval] using ho)
    (by simpa only [tickRuntimeCapacityPolynomial_eval] using hfirst)
    L caller stop wires (by simpa only [hraw] using hin) (by simpa only [htime'] using hout)
  simpa only [hraw,htime',hzero,Nat.zero_add] using hcert

end ShiReversibleGenerator
