import ReversibleExtractionInverseClosingLoopResources
import ReversibleExtractionInverseClosingLoopPayload
import ReversibleExtractionInverseClosingLoopCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Complete real inverse closing pass, with exact original reversed bytes and polynomial resources. -/
theorem extractionInverseClosingLoopTemplate_certificate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (cs : ExtractionTraversalRegister → Nat),
      (∀ q,cs q ≤ bound.eval n) → ∀ start base,
      cs 2=start+cs 22-1 → start+cs 22 ≤ cs 0+1 →
      cs 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) start (cs 22)).map (fun p => p.size+1)).sum →
      3 ≤ cs 20 → cs 17=0 →
      ∀ (L : Type) (caller : L → CounterInstr ExtractionTraversalRegister L) (stop : L) (ys : List Bool),
      let p := extractionInverseClosingLoopTemplate tm
      let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) start (cs 22)
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,
          (((disjoinClosingSuffix base (cs 20+3*cs 22-3) terms).reverse).map (rawAssignmentPayload true)).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs 16=cs 16+41*cs 22 ∧
      p.counters cs 22=0 ∧ p.counters cs 17=0 ∧ ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨budget,hpoly,hexit⟩ := extractionInverseClosingLoopTemplate_resources tm bound
  obtain ⟨clock,hclock⟩ := hpoly
  refine ⟨budget,clock,?_⟩
  intro n cs hb start base hell hlimit hbase hend hbuf L caller stop ys
  dsimp only
  have hr := extractionInverseClosingLoopTemplate_ready tm cs hbuf
  have h := extractionInverseClosingLoopTemplate_run tm L caller stop cs ys hr
  have hp := extractionInverseClosingLoop_payload tm e (cs 22) start base cs hell hlimit hbase hend
  change (extractionInverseClosingLoopTemplate tm).bytes cs=_ at hp
  rw [hp] at h
  exact ⟨h,hclock n cs hb hr,extractionInverseClosingLoopTemplate_count tm cs,
    extractionInverseClosingLoopTemplate_remaining tm cs,
    (extractionInverseClosingLoopTemplate_buffer tm cs).trans hbuf,hexit n cs hb⟩

end ShiReversibleGenerator
