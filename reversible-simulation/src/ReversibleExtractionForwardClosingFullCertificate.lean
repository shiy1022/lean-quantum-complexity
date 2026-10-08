import ReversibleExtractionForwardClosingLoopPolynomial
import ReversibleExtractionForwardClosingCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula

/-- Complete actual forward closing pass: original compiler bytes, real layer count, finite run and polynomial clock. -/
theorem extractionForwardClosingLoopTemplate_certificate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat,∀ n (cs : ExtractionTermRegister → Nat),(∀ q,cs q ≤ bound.eval n) →
      cs 2+cs 9 ≤ cs 0+1 →
      cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9)).map (fun p => p.size+4)).sum →
      cs 17=0 → ∀ (L : Type) (caller : L → CounterInstr ExtractionTermRegister L) (stop : L) (ys : List Bool),
      let p := extractionForwardClosingLoopTemplate tm
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,
          ((disjoinClosingSuffix (cs 18) (cs 20)
            (extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9))).map
              (rawAssignmentPayload false)).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs 16=cs 16+41*cs 9 ∧ p.counters cs 9=0 := by
  obtain ⟨clock,hclock⟩ := extractionForwardClosingLoopTemplate_polynomial tm bound
  refine ⟨clock,?_⟩
  intro n cs hb hlimit hend hbuf L caller stop ys
  dsimp only
  have h := extractionForwardClosingLoopTemplate_counted_run tm e cs hlimit hend hbuf L caller stop ys
  exact ⟨h.1,hclock n cs hb (extractionForwardClosingLoopTemplate_ready tm cs hbuf),h.2⟩

end ShiReversibleGenerator
