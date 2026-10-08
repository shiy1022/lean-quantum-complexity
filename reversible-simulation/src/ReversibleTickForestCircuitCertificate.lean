import ReversibleTickForestQuantumEncoding
import ReversibleTickForestClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- One fixed finite program emits the exact quantum layer bytes, records their count and has a polynomial clock. -/
theorem tickForestTemplate_circuit_certificate (tm : Turing.FinTM2) (inputStride bound : Nat) (backward : Bool)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ bound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (ys : List Bool),
      cs (.inl 1)=capacity.eval n → fixedGuardedEmitterReady (tickTraversalSupply tm) cs →
      CounterBudget cs (.inl 9) (budget.eval n) → TickWindowBudget tm inputStride bound (budget.eval n) cs →
      0 < cs (.inl 1) → cs (.inl 9) ≤ layers.eval n →
      ∀ (L : Type) (caller : L → CounterInstr (FixedLeafRegister (tickTraversalSupply tm)) L) (stop : L) (wires : Nat)
        (hin : ∀ i : Fin (configurationWidth tm (cs (.inl 1))), cs (.inl 0)+inputStride*i.val < cs (tickTraversalSpare tm 2))
        (hout : cs (tickTraversalSpare tm 2)+configurationWidth tm (cs (.inl 1))*(bound+1) ≤ wires),
      let p := tickForestTemplate tm inputStride bound backward
      let gs := tickQuantumLayers tm (cs (.inl 1)) (cs (.inl 0)) inputStride (cs (tickTraversalSpare tm 2)) bound wires hsize hin hout backward
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs (.inl 9)=cs (.inl 9)+gs.length := by
  obtain ⟨clock,hclock⟩ := tickForestTemplate_clock tm inputStride bound backward capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n cs ys hcap hr hb hw hc hl L caller stop wires hin hout
  dsimp only
  have hready := (tickForestTemplate_ready_and_budget tm inputStride bound backward (budget.eval n) cs hr hb hw hc hsize).1
  have hrun := tickForestTemplate_run tm inputStride bound backward L caller stop cs ys hready
  have hbytes := (tickForestTemplate_payload tm inputStride bound backward cs hc).trans
    (tickQuantumLayers_payload tm (cs (.inl 1)) (cs (.inl 0)) inputStride (cs (tickTraversalSpare tm 2)) bound wires hsize hin hout backward)
  rw [hbytes] at hrun
  refine ⟨hrun,hclock n cs hcap hr hb hw hc hl,?_⟩
  rw [tickForestTemplate_count,tickQuantumLayers_length tm _ _ _ _ _ _ hsize hin hout backward hc]

end ShiReversibleGenerator
