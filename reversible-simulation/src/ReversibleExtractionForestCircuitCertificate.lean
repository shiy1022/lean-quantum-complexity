import ReversibleExtractionCleanForestLoopResources
import ReversibleExtractionCleanForestCount
import ReversibleExtractionCleanForestCoordinates
import ReversibleExtractionForestQuantumEncoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Actual complete forward/inverse forest printing, exact finite-wire circuit bytes/count and polynomial clock/exits. -/
theorem extractionCleanForestLoopTemplate_circuit_certificate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (cs : ExtractionForestRegister → Nat),
      (∀ q,cs q ≤ bound.eval n) → cs 26=2*cs 0+1 →
      (if backward then cs 1=0 else cs 1=cs 26-1) →
      ∀ (base wires : Nat),
      (if backward then cs 18=base else cs 18=base+cs 26*(cs 27+1)) →
      ∀ (hsize : extractionBitBound tm (cs 0) ≤ cs 27)
        (hin : ∀ i : Fin (configurationWidth tm (cs 0)),cs 11+stride*i.val < base)
        (hout : base+(2*cs 0+1)*(cs 27+1) ≤ wires)
        (L : Type) (caller : L → CounterInstr ExtractionForestRegister L) (stop : L) (ys : List Bool),
      let p := extractionCleanForestLoopTemplate tm e stride backward
      let gs := extractionForestQuantumLayers tm e (cs 0) (cs 11) stride base (cs 27) wires hsize hin hout backward
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,(gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs 16=cs 16+gs.length ∧
      p.counters cs 26=0 ∧ ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨⟨budget,hexit⟩,⟨clock,hclock⟩⟩ := extractionCleanForestLoopTemplate_resources tm e stride backward bound
  refine ⟨budget,clock,?_⟩
  intro n cs hb hwidth hj base wires hbase hsize hin hout L caller stop ys
  dsimp only
  have hr := extractionCleanForestLoopTemplate_ready tm e stride backward cs
  have hrun := extractionCleanForestLoopTemplate_run tm e stride backward L caller stop cs ys hr
  have hp : (extractionCleanForestLoopTemplate tm e stride backward).bytes cs=
      ((if backward then (extractionForestRawNodes tm e (cs 0) (cs 11) stride base (cs 27)).reverse
        else extractionForestRawNodes tm e (cs 0) (cs 11) stride base (cs 27)).map (rawAssignmentPayload backward)).flatten := by
    cases backward
    · have h := extractionForwardCleanForestLoopTemplate_payload tm e stride base cs hj hbase
      rw [hwidth,extractionOutputRange_original] at h
      exact h
    · have h := extractionInverseCleanForestLoopTemplate_payload tm e stride cs
      rw [hj,hwidth,extractionOutputRange_original,hbase] at h
      exact h
  have hq := extractionForestQuantumLayers_payload tm e (cs 0) (cs 11) stride base (cs 27) wires hsize hin hout backward
  rw [hp.trans hq] at hrun
  refine ⟨hrun,hclock n cs hb hr,?_,extractionCleanForestLoopTemplate_remaining tm e stride backward cs,hexit n cs hb⟩
  rw [extractionForestQuantumLayers_length]
  cases backward
  · have h := extractionForwardCleanForestLoopTemplate_count tm e stride cs hj
    rw [hwidth,extractionOutputRange_original] at h
    exact h
  · have h := extractionInverseCleanForestLoopTemplate_count tm e stride cs
    rw [hj,hwidth,extractionOutputRange_original] at h
    exact h

end ShiReversibleGenerator
