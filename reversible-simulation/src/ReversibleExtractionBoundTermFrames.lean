import ReversibleExtractionTermPrinterFrames
import ReversibleExtractionBoundTermPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator

theorem extractionBoundTermPrinterTemplate_frame (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h3 : q ≠ 3) (h4 : q ≠ 4) (h7 : q ≠ 7) (h8 : q ≠ 8) (h9 : q ≠ 9) (h10 : q ≠ 10)
    (h13 : q ≠ 13) (h14 : q ≠ 14) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h19 : q ≠ 19) (h20 : q ≠ 20) (h21 : q ≠ 21) :
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs q=cs q := by
  change (extractionTermDispatchTemplate tm e backward _).counters
    ((extractionInputSetupTemplate tm stride).counters cs) q=_
  rw [extractionTermDispatchTemplate_frame _ _ _ _ _ _ h3 h13 h14 h15 h16]
  exact extractionInputSetupTemplate_frame tm stride cs q h7 h8 h9 h4 h10 h19 h20 h21

end ShiReversibleGenerator
