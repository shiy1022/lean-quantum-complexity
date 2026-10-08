import ReversibleExtractionTermSchema
import ReversibleFixedNodeProgramTemplate
import ReversibleFormulaSources

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]
open ShiReversibleFormula ShiReversibleTM

/-- Concrete finite emitter for one of the finitely many extraction-term branches. -/
noncomputable def extractionTermPrinterTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R) :
    CounterProgramTemplate R :=
  fixedNodeProgramTemplate r (formulaPrinterTemplates backward (extractionTermSchema tm e first endpoint value) inputs base 0)

theorem extractionTermPrinterTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R) :
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).Embeds :=
  fixedNodeProgramTemplate_embeds _ _

theorem extractionTermPrinterTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R)
    (hr : r.Valid) (hb : r.SourceStable base) (hi : ∀ i,r.SourceStable (inputs i).source) :
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).Runs :=
  fixedNodeProgramTemplate_run _ _ hr (formulaPrinter_operations_valid backward _ inputs base 0 r hr hb hi)

theorem extractionTermPrinterTemplate_polynomial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R)
    (bound : Polynomial Nat) :
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).PolynomiallyTimed bound :=
  fixedNodeProgramTemplate_polynomial _ _ bound

/-- Exact branch payload from the original raw compiler of its finite term schema. -/
theorem extractionTermPrinterTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hb : r.SourceStable base) (hi : ∀ i,r.SourceStable (inputs i).source) (cs : R → Nat) :
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).bytes cs=
      let nodes := (extractionTermSchema tm e first endpoint value).rawCompile (fun i => (inputs i).eval cs) (cs base)
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  have h := formulaPrinter_bytes backward (extractionTermSchema tm e first endpoint value) inputs base 0 r
    hpq hpr hqr (formulaPrinter_stable backward _ inputs base 0 r hb hi) cs
  cases backward <;> simpa only [extractionTermPrinterTemplate,fixedNodeProgramTemplate,Nat.add_zero,Bool.false_eq_true,Bool.true_eq,if_false,if_true] using h

end ShiReversibleGenerator
