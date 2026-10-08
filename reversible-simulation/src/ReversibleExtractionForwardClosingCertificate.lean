import ReversibleExtractionForwardClosingPayload
import ReversibleExtractionForwardClosingLoopReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionForwardClosingLoopTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionTermRegister → Nat) (hlimit : cs 2+cs 9 ≤ cs 0+1)
    (hend : cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9)).map (fun p => p.size+4)).sum) :
    (extractionForwardClosingLoopTemplate tm).bytes cs=
      ((disjoinClosingSuffix (cs 18) (cs 20) (extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9))).map
        (rawAssignmentPayload false)).flatten :=
  extractionForwardClosing_descending_payload tm e (cs 9) cs hlimit hend

/-- One concrete finite run emits the whole original closing suffix and counts exactly41layers per iteration. -/
theorem extractionForwardClosingLoopTemplate_counted_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionTermRegister → Nat) (hlimit : cs 2+cs 9 ≤ cs 0+1)
    (hend : cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9)).map (fun p => p.size+4)).sum)
    (hb : cs 17=0) (L : Type) (caller : L → CounterInstr ExtractionTermRegister L) (stop : L) (ys : List Bool) :
    let p := extractionForwardClosingLoopTemplate tm
    CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
      ⟨some (p.exit stop),p.counters cs,
        ((disjoinClosingSuffix (cs 18) (cs 20) (extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9))).map
          (rawAssignmentPayload false)).flatten++ys⟩ ∧
    p.counters cs 16=cs 16+41*cs 9 ∧ p.counters cs 9=0 := by
  dsimp only
  have h := extractionForwardClosingLoopTemplate_run tm L caller stop cs ys
    (extractionForwardClosingLoopTemplate_ready tm cs hb)
  rw [extractionForwardClosingLoopTemplate_payload tm e cs hlimit hend] at h
  exact ⟨h,extractionForwardClosingLoopTemplate_count tm cs,extractionForwardClosingLoopTemplate_remaining tm cs⟩

end ShiReversibleGenerator
