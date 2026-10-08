import ReversibleExtractionBoundTermClock
import ReversibleExtractionBoundTermPayload
import ReversibleExtractionBoundTermLayerCount

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- A complete selected term is printed by one actual counted finite run, with exact bytes and layer count,
including its real cleanup, subtraction and source-address computations. -/
theorem extractionBoundTermPrinterTemplate_certificate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : ExtractionTermRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
      cs 2 ≤ cs 0 → cs 5=0 → cs 6=0 → cs 17=0 →
      ∀ (L : Type) (caller : L → CounterInstr ExtractionTermRegister L) (stop : L) (ys : List Bool),
      let p := extractionBoundTermPrinterTemplate tm e stride backward
      let term := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
      let nodes := term.rawCompile
        (fun i => cs 11+stride*naturalConfigurationAddress tm (cs 0) (naturalInputAddress tm (cs 0) i)) (cs 18)
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,
          ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs 16=cs 16+formulaElementaryLayers term := by
  obtain ⟨clock,hclock⟩ := extractionBoundTermPrinterTemplate_polynomial tm e stride backward bound
  refine ⟨clock,?_⟩
  intro n cs hb hell h5 h6 h17 L caller stop ys
  dsimp only
  have hready := extractionBoundTermPrinterTemplate_ready tm e stride backward cs h5 h6 h17
  have hrun := extractionBoundTermPrinterTemplate_run tm e stride backward L caller stop cs ys hready
  rw [extractionBoundTermPrinterTemplate_payload tm e stride backward cs hell] at hrun
  exact ⟨hrun,hclock n cs hb hready,extractionBoundTermPrinterTemplate_count tm e stride backward cs hell⟩

end ShiReversibleGenerator
