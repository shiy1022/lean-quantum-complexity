import ReversibleTickForwardHistoryPayload
import ReversibleTickForwardHistoryCounters
import ReversibleTickForwardHistoryClock
import ReversibleTickStridedHistoryQuantumEncoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Actual boundary-inclusive forward history has exact quantum bytes/count and a polynomial clock. -/
theorem tickForwardHistoryTemplate_circuit_certificate (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n firstOutput (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ys : List Bool),
      TickRetreatHistoryBudget tm bound (budget.eval n) (capacity.eval n) (layers.eval n) firstOutput
        (cs (tickTraversalSpare tm 3)) cs → 0 < capacity.eval n →
      firstOutput=cs (tickTraversalSpare tm 6)+18*configurationWidth tm (capacity.eval n) →
      cs (tickTraversalSpare tm 6)+17+18*configurationWidth tm (capacity.eval n) ≤ budget.eval n →
      cs (tickTraversalSpare tm 6)+18*configurationWidth tm (capacity.eval n)+
        configurationWidth tm (capacity.eval n)*(bound+1) ≤ budget.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (wires : Nat)
        (hin : ∀ i : Fin (configurationWidth tm (capacity.eval n)),cs (tickTraversalSpare tm 6)+17+18*i.val < firstOutput)
        (hout : firstOutput+(cs (tickTraversalSpare tm 3)+1)*
          (configurationWidth tm (capacity.eval n)*(bound+1)) ≤ wires),
      let p := tickForwardHistoryTemplate tm bound
      let gs := tickStridedHistoryQuantumLayers tm (capacity.eval n) (cs (tickTraversalSpare tm 6)+17) 18
        firstOutput bound (cs (tickTraversalSpare tm 3)+1) wires hsize hin hout false
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inl 9)=cs (.inl 9)+gs.length ∧
      p.counters cs (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickForwardHistoryTemplate_clock tm bound capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n firstOutput cs ys hs hc hfirst hi ho L caller stop wires hin hout
  dsimp only
  have hready := tickForwardHistoryTemplate_ready tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstOutput cs hs hc hsize hi ho
  have hrun := tickForwardHistoryTemplate_run tm bound L caller stop cs ys hready
  have hbytes := (tickForwardHistoryTemplate_payload tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstOutput cs hs hc hsize hfirst).trans
    (tickStridedHistoryQuantumLayers_payload tm (capacity.eval n) (cs (tickTraversalSpare tm 6)+17) 18 firstOutput
      bound (cs (tickTraversalSpare tm 3)+1) wires hsize hin hout false)
  rw [hbytes] at hrun
  refine ⟨hrun,hclock n firstOutput cs hs hc hi ho,?_,tickForwardHistoryTemplate_remaining tm bound cs⟩
  rw [tickForwardHistoryTemplate_count,hs.2.2.1,
    tickStridedHistoryQuantumLayers_length tm _ _ _ _ _ _ _ hsize hin hout false hc]

end ShiReversibleGenerator
