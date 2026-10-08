import ReversibleOutputCopyLoopQuantum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- One finite output-copy traversal has exact CNOT bytes/counts, an actual polynomial clock, and a cleared loop counter. -/
theorem outputCopyLoopTemplate_circuit_certificate (budget : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : OutputCopyRegister → Nat),
      (∀ q,cs q ≤ budget.eval n) → cs 3=0 → cs 4=0 →
      ∀ (L : Type) (caller : L → CounterInstr OutputCopyRegister L) (stop : L) (ys : List Bool)
        (wires outputBase : Nat) (hs : cs 0 < outputBase) (ho : outputBase+cs 6 ≤ wires)
        (ht : cs 1=outputBase+cs 6-1),
      let gs := outputCopyQuantumLayers wires outputBase (cs 5) (cs 6) (cs 0) hs ho
      CounterRun (outputCopyLoopTemplate.code caller stop)
        ⟨some (outputCopyLoopTemplate.entry stop),cs,ys⟩ (outputCopyLoopTemplate.steps cs)
        ⟨some (outputCopyLoopTemplate.exit stop),outputCopyLoopTemplate.counters cs,
          (gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      outputCopyLoopTemplate.steps cs ≤ clock.eval n ∧
      outputCopyLoopTemplate.counters cs 2=cs 2+gs.length ∧ outputCopyLoopTemplate.counters cs 6=0 := by
  obtain ⟨clock,hclock⟩ := outputCopyLoopTemplate_polynomial budget
  refine ⟨clock,?_⟩
  intro n cs hb hbuf htmp L caller stop ys wires outputBase hs ho ht
  dsimp only
  have hr := outputCopyLoopTemplate_ready cs hbuf htmp
  have hrun := outputCopyLoopTemplate_run L caller stop cs ys hr
  rw [outputCopyLoopTemplate_quantum_payload cs wires outputBase hs ho ht] at hrun
  have hc := outputCopyLoopTemplate_pointer_count_result cs
  refine ⟨hrun,hclock n cs hb hr,?_,hc.2.2.2.2⟩
  rw [outputCopyQuantumLayers_length]
  exact hc.2.2.1

end ShiReversibleGenerator
