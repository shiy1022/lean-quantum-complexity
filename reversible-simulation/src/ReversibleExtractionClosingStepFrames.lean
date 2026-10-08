import ReversibleExtractionClosingStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The real loop body frames its remaining-iterations register and output buffer. -/
theorem extractionClosingStepTemplate_frame (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h2 : q ≠ 2) (h3 : q ≠ 3) (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) (h12 : q ≠ 12)
    (h13 : q ≠ 13) (h14 : q ≠ 14) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h18 : q ≠ 18) (h19 : q ≠ 19) (h20 : q ≠ 20) (h21 : q ≠ 21) :
    (extractionClosingStepTemplate tm backward).counters cs q=cs q := by
  change extractionClosingAdvanceTemplate.counters ((extractionBoundClosingPrinterTemplate tm backward).counters cs) q=_
  rw [extractionClosingAdvanceTemplate_counters]
  simp only [Function.update_of_ne h2,Function.update_of_ne h21,Function.update_of_ne h20,
    Function.update_of_ne h19,Function.update_of_ne h18]
  exact extractionBoundClosingPrinterTemplate_frame tm backward cs q h3 h5 h6 h7 h12 h13 h14 h15 h16 h19 h21

end ShiReversibleGenerator
