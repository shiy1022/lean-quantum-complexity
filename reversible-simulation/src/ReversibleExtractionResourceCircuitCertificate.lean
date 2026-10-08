import ReversibleExtractionResourcePayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual prelude endpoint and finite setup derive every wire coordinate of the full original extraction circuit. -/
theorem extractionResourceTemplate_circuit_certificate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (time : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (cs : ExtractionMasterRegister → Nat),
      (∀ r,cs (.inl r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r) →
      (∀ q : ExtractionForestRegister,cs (.inr q)=0) →
      ∀ (ht : 0 < time.eval n) (L : Type) (caller : L → CounterInstr ExtractionMasterRegister L) (stop : L) (ys : List Bool),
      let cap := n+time.eval n*machinePushBound tm+1
      let base := n+18*configurationWidth tm cap+time.eval n*(configurationWidth tm cap*(tickSizeBound tm+1))
      let source := base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm
      let wires := n+paddedMachineWorkspace tm n (time.eval n)+(2*cap+1)
      let hin : ∀ i : Fin (configurationWidth tm cap),source+(tickSizeBound tm+1)*i.val < base :=
        extractionFinalSource_lt_base tm n (time.eval n) ht
      let hout : base+(2*cap+1)*(extractionBitBound tm cap+1) ≤ wires :=
        (by rw [extractionForestEnd_eq_output]; exact Nat.le_add_right _ _)
      let gs := extractionForestQuantumLayers tm e cap source (tickSizeBound tm+1) base (extractionBitBound tm cap)
        wires (Nat.le_refl _) hin hout backward
      let p := extractionResourceTemplate tm e backward
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inr 16)=gs.length ∧
      ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨⟨budget,hexit⟩,⟨clock,hclock⟩⟩ := extractionResourceTemplate_resources tm e backward (resourceCounterBudgetPolynomial tm time)
  refine ⟨budget,clock,?_⟩
  intro n cs hpull houtside ht L caller stop ys
  dsimp only
  let cap := n+time.eval n*machinePushBound tm+1
  let base := n+18*configurationWidth tm cap+time.eval n*(configurationWidth tm cap*(tickSizeBound tm+1))
  let source := base-configurationWidth tm cap*(tickSizeBound tm+1)+tickSizeBound tm
  let wires := n+paddedMachineWorkspace tm n (time.eval n)+(2*cap+1)
  have hin : ∀ i : Fin (configurationWidth tm cap),source+(tickSizeBound tm+1)*i.val < base :=
    extractionFinalSource_lt_base tm n (time.eval n) ht
  have hout : base+(2*cap+1)*(extractionBitBound tm cap+1) ≤ wires := by
    have he := extractionForestEnd_eq_output tm n (time.eval n)
    change base+(2*cap+1)*(extractionBitBound tm cap+1)=n+paddedMachineWorkspace tm n (time.eval n) at he
    rw [he]
    exact Nat.le_add_right _ _
  have hb := extractionResourcePrelude_uniform_bound tm time n cs hpull houtside
  have hr := extractionResourceTemplate_ready tm e backward cs
  have hrun := extractionResourceTemplate_run tm e backward L caller stop cs ys hr
  have hp := extractionResourceTemplate_payload_count tm e backward n (time.eval n) cs hpull
  dsimp only at hp
  have hq := extractionForestQuantumLayers_payload tm e cap source (tickSizeBound tm+1) base (extractionBitBound tm cap)
    wires (Nat.le_refl _) hin hout backward
  rw [hp.1.trans hq] at hrun
  refine ⟨hrun,hclock n cs hb hr,?_,hexit n cs hb⟩
  exact hp.2.trans (extractionForestQuantumLayers_length tm e cap source (tickSizeBound tm+1) base
    (extractionBitBound tm cap) wires (Nat.le_refl _) hin hout backward).symm

end ShiReversibleGenerator
