import ReversibleTickResourceInverseCircuitCertificate
import ReversibleTickResourceForwardWireCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- No wire-layout premise remains for printing inverse history on the concrete complete-machine register count. -/
theorem tickResourceInverse_full_wire_certificate (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r) →
      (∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) → 0 < time.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (ys : List Bool),
      let cap := (tickRuntimeCapacityPolynomial tm time).eval n
      let firstOutput := n+18*configurationWidth tm cap
      let wires := n+paddedMachineWorkspace tm n (time.eval n)+(2*cap+1)
      let start := tickResourceInverseStart tm cs
      let p := tickInverseHistoryTemplate tm (tickSizeBound tm)
      let hin : ∀ i : Fin (configurationWidth tm cap),n+17+18*i.val < firstOutput := by
        intro i
        have hi := i.isLt
        omega
      let hout : firstOutput+time.eval n*(configurationWidth tm cap*(tickSizeBound tm+1)) ≤ wires := by
        have h := tickPreparedEnd_le_workspace tm n (time.eval n)
        rw [←tickRuntimeCapacityPolynomial_eval tm time n] at h
        exact h.trans (Nat.le_add_right _ _)
      let gs := tickStridedHistoryQuantumLayers tm cap (n+17) 18 firstOutput (tickSizeBound tm)
        (time.eval n) wires (Nat.le_refl _) hin hout true
      CounterRun (p.code caller stop) ⟨some (p.entry stop),start,ys⟩ (p.steps start)
        ⟨some (p.exit stop),p.counters start,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps start ≤ clock.eval n ∧ p.counters start (.inl 9)=gs.length ∧
      p.counters start (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickResourceInverse_circuit_certificate tm time
  refine ⟨clock,?_⟩
  intro n cs hpull houtside ht L caller stop ys
  dsimp only
  have hout : n+18*configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)+
      time.eval n*(configurationWidth tm ((tickRuntimeCapacityPolynomial tm time).eval n)*(tickSizeBound tm+1)) ≤
      n+paddedMachineWorkspace tm n (time.eval n)+(2*(tickRuntimeCapacityPolynomial tm time).eval n+1) := by
    have h := tickPreparedEnd_le_workspace tm n (time.eval n)
    rw [←tickRuntimeCapacityPolynomial_eval tm time n] at h
    exact h.trans (Nat.le_add_right _ _)
  exact hclock n cs hpull houtside ht L caller stop ys _ hout

end ShiReversibleGenerator
