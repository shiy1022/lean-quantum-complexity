import ReversibleTickForwardIterationQuantumEncoding
import ReversibleTickRetreatIterationPayloadAgreement
import ReversibleTickRetreatIterationClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Actual late-to-early history traversal emits the exact chronological forward quantum circuit. -/
theorem tickRetreatIterationTemplate_circuit_certificate (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n firstInput firstOutput (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ys : List Bool),
      TickRetreatIterationBudget tm bound (budget.eval n) (capacity.eval n) (layers.eval n) firstInput firstOutput
        (cs (tickTraversalSpare tm 3)) cs → 0 < capacity.eval n →
      firstInput+configurationWidth tm (capacity.eval n)*(bound+1)=firstOutput+bound →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (wires : Nat)
        (hin : ∀ i : Fin (configurationWidth tm (capacity.eval n)),
          firstInput+configurationWidth tm (capacity.eval n)*(bound+1)+(bound+1)*i.val <
            firstOutput+configurationWidth tm (capacity.eval n)*(bound+1))
        (hout : firstOutput+configurationWidth tm (capacity.eval n)*(bound+1)+cs (tickTraversalSpare tm 3)*
          (configurationWidth tm (capacity.eval n)*(bound+1)) ≤ wires),
      let p := tickRetreatIterationTemplate tm bound
      let gs := tickForwardIterationQuantumLayers tm (capacity.eval n)
        (firstInput+configurationWidth tm (capacity.eval n)*(bound+1))
        (firstOutput+configurationWidth tm (capacity.eval n)*(bound+1)) bound (cs (tickTraversalSpare tm 3)) wires hsize hin hout
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inl 9)=cs (.inl 9)+gs.length := by
  obtain ⟨clock,hclock⟩ := tickRetreatIterationTemplate_clock tm bound capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n firstInput firstOutput cs ys hs hc hcompatible L caller stop wires hin hout
  dsimp only
  have hready := tickRetreatIterationTemplate_ready tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstInput firstOutput cs hs hc hsize
  have hrun := tickRetreatIterationTemplate_run tm bound L caller stop cs ys hready
  have hbytes := (tickRetreatIterationTemplate_payload tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    firstInput firstOutput cs hs hc hsize hcompatible).trans
    (tickForwardIterationQuantumLayers_payload tm (capacity.eval n)
      (firstInput+configurationWidth tm (capacity.eval n)*(bound+1))
      (firstOutput+configurationWidth tm (capacity.eval n)*(bound+1)) bound (cs (tickTraversalSpare tm 3)) wires hsize hin hout)
  rw [hbytes] at hrun
  refine ⟨hrun,hclock n firstInput firstOutput cs hs hc,?_⟩
  rw [tickRetreatIterationTemplate_count,hs.2.2.1,
    tickForwardIterationQuantumLayers_length tm _ _ _ _ _ _ hsize hin hout hc]

end ShiReversibleGenerator
