import ReversibleExtractionTermPrinter
import ReversibleFormulaLayerCount

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- The finite schema printer increments its real count by exactly the schema's elementary quantum layers. -/
theorem extractionTermPrinterTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R)
    (hp : r.count ≠ r.p) (hq : r.count ≠ r.q) (hr : r.count ≠ r.r) (cs : R → Nat) :
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).counters cs r.count=
      cs r.count+formulaElementaryLayers (extractionTermSchema tm e first endpoint value) :=
  formulaPrinter_counter_count backward _ inputs base 0 r hp hq hr cs

end ShiReversibleGenerator
