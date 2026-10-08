import ReversibleTickInverseHistoryCounters
import ReversibleTickStridedHistoryQuantumEncoding
import ReversibleTickInverseHistoryClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual boundary-inclusive inverse history has exact quantum bytes/count and a polynomial clock. -/
theorem tickInverseHistoryTemplate_circuit_certificate (tm : Turing.FinTM2) (bound : Nat)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ys : List Bool),
      fixedGuardedEmitterReady (tickTraversalSupply tm) cs → CounterBudget cs (.inl 9) (budget.eval n) →
      TickWindowBudget tm 18 bound (budget.eval n) cs → cs (.inl 1)=capacity.eval n →
      0 < capacity.eval n → 0 < cs (tickTraversalSpare tm 7) →
      cs (.inl 9)+cs (tickTraversalSpare tm 7)*tickForestLayerCount tm (capacity.eval n) ≤ layers.eval n →
      cs (tickTraversalSpare tm 2)+(cs (tickTraversalSpare tm 7)+1)*
        (configurationWidth tm (capacity.eval n)*(bound+1)) ≤ budget.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (wires : Nat)
        (hin : ∀ i : Fin (configurationWidth tm (cs (.inl 1))),cs (.inl 0)+18*i.val < cs (tickTraversalSpare tm 2))
        (hout : cs (tickTraversalSpare tm 2)+cs (tickTraversalSpare tm 7)*
          (configurationWidth tm (cs (.inl 1))*(bound+1)) ≤ wires),
      let p := tickInverseHistoryTemplate tm bound
      let gs := tickStridedHistoryQuantumLayers tm (cs (.inl 1)) (cs (.inl 0)) 18
        (cs (tickTraversalSpare tm 2)) bound (cs (tickTraversalSpare tm 7)) wires hsize hin hout true
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inl 9)=cs (.inl 9)+gs.length ∧
      p.counters cs (tickTraversalSpare tm 3)=0 := by
  obtain ⟨clock,hclock⟩ := tickInverseHistoryTemplate_clock tm bound capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n cs ys hr hb hw hcap hc ht hl hf L caller stop wires hin hout
  dsimp only
  have hpos : 0 < cs (.inl 1) := by rw [hcap]; exact hc
  have hready := tickInverseHistoryTemplate_ready tm bound (budget.eval n) (capacity.eval n) (layers.eval n)
    cs hr hb hw hcap hc hsize ht hl hf
  have hrun := tickInverseHistoryTemplate_run tm bound L caller stop cs ys hready
  have hbytes := (tickInverseHistoryTemplate_payload tm bound cs hpos ht).trans
    (tickStridedHistoryQuantumLayers_payload tm (cs (.inl 1)) (cs (.inl 0)) 18 (cs (tickTraversalSpare tm 2))
      bound (cs (tickTraversalSpare tm 7)) wires hsize hin hout true)
  rw [hbytes] at hrun
  refine ⟨hrun,hclock n cs hr hb hw hcap hc ht hl hf,?_,tickInverseHistoryTemplate_remaining tm bound cs⟩
  rw [tickInverseHistoryTemplate_count tm bound cs ht,
    tickStridedHistoryQuantumLayers_length tm _ _ _ _ _ _ _ hsize hin hout true hpos]

end ShiReversibleGenerator
