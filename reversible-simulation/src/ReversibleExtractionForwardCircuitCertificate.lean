import ReversibleExtractionForwardPassPayload
import ReversibleExtractionForwardPassCount
import ReversibleExtractionQuantumEncoding
import ReversibleInitializationExactLayers

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Actual forward extraction emits precisely the established finite-wire forward circuit, with its real count and clock. -/
theorem extractionForwardPassTemplate_circuit_certificate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (cs : ExtractionTraversalRegister → Nat),
      (∀ q,cs q ≤ bound.eval n) → cs 2=0 → cs 9=cs 0+1 →
      cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)).map (fun p => p.size+4)).sum →
      cs 17=0 →
      ∀ (L : Type) (caller : L → CounterInstr ExtractionTraversalRegister L) (stop : L) (ys : List Bool)
        (wires : Nat) (hin : ∀ i : Fin (configurationWidth tm (cs 0)),cs 11+stride*i.val < cs 18)
        (hout : cs 18+(extractionFormula tm e (cs 0) (cs 1)).size ≤ wires),
      let p := extractionForwardPassTemplate tm e stride
      let gs := extractionQuantumLayers tm e (cs 0) (cs 1) (cs 11) stride (cs 18) wires hin hout false
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs 16=cs 16+gs.length ∧
      ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨⟨budget,hexit⟩,⟨clock,hclock⟩⟩ := extractionForwardPassTemplate_resources tm e stride bound
  refine ⟨budget,clock,?_⟩
  intro n cs hb hell hcount hend hbuf L caller stop ys wires hin hout
  dsimp only
  have hr := extractionForwardPassTemplate_ready tm e stride cs hbuf
  have hrun := extractionForwardPassTemplate_run tm e stride L caller stop cs ys hr
  have hp := extractionForwardPassTemplate_payload tm e stride cs hell hcount hend
  rw [extractionRawNodes_natural] at hp
  have hq := extractionQuantumLayers_payload tm e (cs 0) (cs 1) (cs 11) stride (cs 18) wires hin hout false
  change ((extractionRawNodes tm e (cs 0) (cs 1) (cs 11) stride (cs 18)).map
    (rawAssignmentPayload false)).flatten=_ at hq
  rw [hp.trans hq] at hrun
  refine ⟨hrun,hclock n cs hb hr,?_,hexit n cs hb⟩
  rw [extractionForwardPassTemplate_count tm e stride cs hcount,
    extractionNaturalFormula_original,formulaElementaryLayers_rename,
    extractionQuantumLayers_length]

end ShiReversibleGenerator
