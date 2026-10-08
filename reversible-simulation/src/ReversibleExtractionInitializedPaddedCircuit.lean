import ReversibleExtractionInitializedPaddedPayload
import ReversibleExtractionPaddedQuantumEncoding

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Initialized runtime extraction needs only actual wire-layout facts; its size, roots, buffers and pass metadata are computed. -/
theorem extractionInitializedPaddedLeafTemplate_circuit_certificate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (cs : ExtractionPaddedRegister → Nat),
      (∀ q,cs q ≤ bound.eval n) →
      ∀ (wires : Nat) (hsize : (extractionFormula tm e (cs 0) (cs 1)).size ≤ cs 4)
        (hin : ∀ i : Fin (configurationWidth tm (cs 0)),cs 11+stride*i.val < cs 18)
        (hout : cs 18+cs 4+1 ≤ wires)
        (L : Type) (caller : L → CounterInstr ExtractionPaddedRegister L) (stop : L) (ys : List Bool),
      let p := extractionInitializedPaddedLeafTemplate tm e stride backward
      let gs := extractionPaddedQuantumLayers tm e (cs 0) (cs 1) (cs 11) stride (cs 18) (cs 4) wires hsize hin hout backward
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs 16=cs 16+gs.length ∧
      ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨⟨budget,hexit⟩,⟨clock,hclock⟩⟩ := extractionInitializedPaddedLeafTemplate_resources tm e stride backward bound
  refine ⟨budget,clock,?_⟩
  intro n cs hb wires hsize hin hout L caller stop ys
  dsimp only
  have hr := extractionInitializedPaddedLeafTemplate_ready tm e stride backward cs
  have hrun := extractionInitializedPaddedLeafTemplate_run tm e stride backward L caller stop cs ys hr
  have hp := extractionInitializedPaddedLeafTemplate_payload tm e stride backward cs
  have hq := extractionPaddedQuantumLayers_payload tm e (cs 0) (cs 1) (cs 11) stride (cs 18) (cs 4) wires hsize hin hout backward
  rw [hp.trans hq] at hrun
  refine ⟨hrun,hclock n cs hb hr,?_,hexit n cs hb⟩
  rw [extractionPaddedQuantumLayers_length]
  exact extractionInitializedPaddedLeafTemplate_count tm e stride backward cs

end ShiReversibleGenerator
