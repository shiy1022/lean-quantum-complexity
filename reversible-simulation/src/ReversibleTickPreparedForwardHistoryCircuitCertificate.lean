import ReversibleTickPreparedForwardHistoryPayload
import ReversibleTickPreparedForwardHistoryCounters
import ReversibleTickPreparedForwardHistoryClock
import ReversibleTickStridedHistoryQuantumEncoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- A finite complete forward emitter has exact circuit bytes/count and actual polynomial runtime from metadata. -/
theorem tickPreparedForwardHistoryTemplate_circuit_certificate (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n firstOutput (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ys : List Bool),
      fixedGuardedEmitterReady (tickTraversalSupply tm) cs → CounterBudget cs (.inl 9) (budget.eval n) →
      cs (.inl 1)=capacity.eval n → 0 < capacity.eval n → 0 < cs (tickTraversalSpare tm 7) →
      cs (tickTraversalSpare tm 1)=firstOutput+cs (tickTraversalSpare tm 7)*
        (configurationWidth tm (capacity.eval n)*(bound+1)) →
      cs (tickTraversalSpare tm 1)+bound ≤ budget.eval n →
      cs (.inl 9)+(cs (tickTraversalSpare tm 7)-1)*tickForestLayerCount tm (capacity.eval n) ≤ layers.eval n →
      cs (tickTraversalSpare tm 6)+17+18*configurationWidth tm (capacity.eval n) ≤ budget.eval n →
      cs (tickTraversalSpare tm 6)+18*configurationWidth tm (capacity.eval n)+
        configurationWidth tm (capacity.eval n)*(bound+1) ≤ budget.eval n →
      firstOutput=cs (tickTraversalSpare tm 6)+18*configurationWidth tm (capacity.eval n) →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (wires : Nat)
        (hin : ∀ i : Fin (configurationWidth tm (capacity.eval n)),cs (tickTraversalSpare tm 6)+17+18*i.val < firstOutput)
        (hout : firstOutput+cs (tickTraversalSpare tm 7)*
          (configurationWidth tm (capacity.eval n)*(bound+1)) ≤ wires),
      let p := tickPreparedForwardHistoryTemplate tm bound
      let gs := tickStridedHistoryQuantumLayers tm (capacity.eval n) (cs (tickTraversalSpare tm 6)+17) 18
        firstOutput bound (cs (tickTraversalSpare tm 7)) wires hsize hin hout false
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inl 9)=cs (.inl 9)+gs.length ∧
      p.counters cs (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickPreparedForwardHistoryTemplate_clock tm bound capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n firstOutput cs ys hr hb hcap hc ht hend hbound hlayers hi ho hfirst L caller stop wires hin hout
  dsimp only
  have hready := tickPreparedForwardHistoryTemplate_ready tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstOutput cs hr hb hcap hc hsize ht hend hbound hlayers hi ho
  have hrun := tickPreparedForwardHistoryTemplate_run tm bound L caller stop cs ys hready
  have hbytes := (tickPreparedForwardHistoryTemplate_payload tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstOutput cs hr hb hcap hc hsize ht hend hbound hlayers hfirst).trans
    (tickStridedHistoryQuantumLayers_payload tm (capacity.eval n) (cs (tickTraversalSpare tm 6)+17) 18 firstOutput
      bound (cs (tickTraversalSpare tm 7)) wires hsize hin hout false)
  rw [hbytes] at hrun
  refine ⟨hrun,hclock n firstOutput cs hr hb hcap hc ht hend hbound hlayers hi ho,?_,
    tickPreparedForwardHistoryTemplate_remaining tm bound cs⟩
  rw [tickPreparedForwardHistoryTemplate_count tm bound cs ht,hcap,
    tickStridedHistoryQuantumLayers_length tm _ _ _ _ _ _ _ hsize hin hout false hc]

end ShiReversibleGenerator
