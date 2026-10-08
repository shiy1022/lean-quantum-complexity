import ReversibleExtractionForwardPrefixLoopResources
import ReversibleExtractionForwardPrefixCertificate

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Complete actual forward prefix: original compiler bytes, exact layer count, zero buffer, polynomial clock and exits. -/
theorem extractionForwardPrefixLoopTemplate_certificate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget clock : Polynomial Nat,∀ n (cs : ExtractionTraversalRegister → Nat),
      (∀ q,cs q ≤ bound.eval n) → ∀ base,
      cs 22 ≤ cs 0+1 → cs 2=cs 22-1 →
      cs 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 22)).map (fun p => p.size+1)).sum →
      cs 17=0 → ∀ (L : Type) (caller : L → CounterInstr ExtractionTraversalRegister L) (stop : L) (ys : List Bool),
      let p := extractionForwardPrefixLoopTemplate tm e stride
      let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 22)
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,
          ((disjoinTermPrefix (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit)
            base terms).map (rawAssignmentPayload false)).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧
      p.counters cs 16=cs 16+(terms.map (fun p => formulaElementaryLayers p+2)).sum ∧
      p.counters cs 22=0 ∧ p.counters cs 17=0 ∧ ∀ q,p.counters cs q ≤ budget.eval n := by
  obtain ⟨budget,hpoly,hexit⟩ := extractionForwardPrefixLoopTemplate_resources tm e stride bound
  obtain ⟨clock,hclock⟩ := hpoly
  refine ⟨budget,clock,?_⟩
  intro n cs hb base hk hell hend hbuf L caller stop ys
  dsimp only
  have h := extractionForwardPrefixLoopTemplate_counted_run tm e stride cs base hk hell hend hbuf L caller stop ys
  exact ⟨h.1,hclock n cs hb (extractionForwardPrefixLoopTemplate_ready tm e stride cs hbuf),
    h.2.1,h.2.2.1,h.2.2.2,hexit n cs hb⟩

end ShiReversibleGenerator
