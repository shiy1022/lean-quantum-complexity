import ReversibleTickIterationQuantumEncoding
import ReversibleTickInverseAdvanceIterationClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual finite inverse history emitter has exact quantum bytes/count and a polynomial clock. -/
theorem tickInverseAdvanceIterationTemplate_circuit_certificate (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ys : List Bool),
      TickForwardIterationLayerBudget tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
        (cs (tickTraversalSpare tm 3)) cs → 0 < capacity.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (wires : Nat)
        (hin : ∀ i : Fin (configurationWidth tm (cs (.inl 1))),
          cs (.inl 0)+(bound+1)*i.val < cs (tickTraversalSpare tm 2))
        (hout : cs (tickTraversalSpare tm 2)+cs (tickTraversalSpare tm 3)*
          (configurationWidth tm (cs (.inl 1))*(bound+1)) ≤ wires),
      let p := tickInverseAdvanceIterationTemplate tm bound
      let gs := tickInverseIterationQuantumLayers tm (cs (.inl 1)) (cs (.inl 0)) (cs (tickTraversalSpare tm 2))
        bound (cs (tickTraversalSpare tm 3)) wires hsize hin hout
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inl 9)=cs (.inl 9)+gs.length := by
  obtain ⟨clock,hclock⟩ := tickInverseAdvanceIterationTemplate_clock tm bound capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n cs ys hs hc L caller stop wires hin hout
  dsimp only
  have hpos : 0 < cs (.inl 1) := by rw [hs.1.2.2.1]; exact hc
  have hready := tickInverseAdvanceIterationTemplate_ready tm bound (budget.eval n) (capacity.eval n) cs hs.1 hc hsize
  have hrun := tickInverseAdvanceIterationTemplate_run tm bound L caller stop cs ys hready
  have hbytes := (tickInverseAdvanceIterationTemplate_symbolic_payload tm bound cs).trans
    ((tickInverseIterationBytes_agreement tm bound (cs (.inl 1)) (cs (tickTraversalSpare tm 3))
      (cs (.inl 0)) (cs (tickTraversalSpare tm 2)) hpos).trans
      (tickInverseIterationQuantumLayers_payload tm (cs (.inl 1)) (cs (.inl 0)) (cs (tickTraversalSpare tm 2))
        bound (cs (tickTraversalSpare tm 3)) wires hsize hin hout))
  rw [hbytes] at hrun
  refine ⟨hrun,hclock n cs hs hc,?_⟩
  rw [tickInverseAdvanceIterationTemplate_count,
    tickInverseIterationQuantumLayers_length tm _ _ _ _ _ _ hsize hin hout hpos]

end ShiReversibleGenerator
