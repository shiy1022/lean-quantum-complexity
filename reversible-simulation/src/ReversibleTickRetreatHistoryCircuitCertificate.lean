import ReversibleTickForwardIterationQuantumEncoding
import ReversibleTickRetreatHistoryPayloadAgreement
import ReversibleTickRetreatIterationCounts
import ReversibleTickRetreatHistoryClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Actual late-to-early history traversal emits the exact chronological forward quantum circuit. -/
theorem tickRetreatHistoryTemplate_circuit_certificate (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n firstOutput (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ys : List Bool),
      TickRetreatHistoryBudget tm bound (budget.eval n) (capacity.eval n) (layers.eval n) firstOutput
        (cs (tickTraversalSpare tm 3)) cs → 0 < capacity.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (wires : Nat)
        (hin : ∀ i : Fin (configurationWidth tm (capacity.eval n)),
          firstOutput+bound+(bound+1)*i.val <
            firstOutput+configurationWidth tm (capacity.eval n)*(bound+1))
        (hout : firstOutput+configurationWidth tm (capacity.eval n)*(bound+1)+cs (tickTraversalSpare tm 3)*
          (configurationWidth tm (capacity.eval n)*(bound+1)) ≤ wires),
      let p := tickRetreatIterationTemplate tm bound
      let gs := tickForwardIterationQuantumLayers tm (capacity.eval n)
        (firstOutput+bound)
        (firstOutput+configurationWidth tm (capacity.eval n)*(bound+1)) bound (cs (tickTraversalSpare tm 3)) wires hsize hin hout
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inl 9)=cs (.inl 9)+gs.length := by
  obtain ⟨clock,hclock⟩ := tickRetreatHistoryTemplate_clock tm bound capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n firstOutput cs ys hs hc L caller stop wires hin hout
  dsimp only
  have hready := tickRetreatHistoryTemplate_ready tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstOutput cs hs hc hsize
  have hrun := tickRetreatIterationTemplate_run tm bound L caller stop cs ys hready
  have hbytes := (tickRetreatHistoryTemplate_payload tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstOutput cs hs hc hsize).trans
    (tickForwardIterationQuantumLayers_payload tm (capacity.eval n)
      (firstOutput+bound)
      (firstOutput+configurationWidth tm (capacity.eval n)*(bound+1)) bound (cs (tickTraversalSpare tm 3)) wires hsize hin hout)
  rw [hbytes] at hrun
  refine ⟨hrun,hclock n firstOutput cs hs hc,?_⟩
  rw [tickRetreatIterationTemplate_count,hs.2.2.1,
    tickForwardIterationQuantumLayers_length tm _ _ _ _ _ _ hsize hin hout hc]

end ShiReversibleGenerator
