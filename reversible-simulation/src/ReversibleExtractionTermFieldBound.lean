import ReversibleFormulaPrinterFieldBound
import ReversibleExtractionTermPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

noncomputable def extractionTermSchemaBudget (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) : Nat :=
  10+(unaryTable (outputCellBool e) (fun a => (Formula.input (.inr a) : Formula (ExtractionTermInput tm))) true).size

theorem extractionTermSchema_size_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (first endpoint : Bool) (value : ExtractionValueKind) :
    (extractionTermSchema tm e first endpoint value).size ≤ extractionTermSchemaBudget tm e := by
  cases first <;> cases endpoint <;> cases value <;>
    simp [extractionTermSchema,extractionTermSchemaBudget,Formula.size] <;> omega

/-- Every term branch resets its printer fields, with a bound independent of their old contents. -/
theorem extractionTermPrinterTemplate_fields_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hcp : r.count ≠ r.p) (hcq : r.count ≠ r.q) (hcr : r.count ≠ r.r)
    (hsb : r.SourceStable base) (hsi : ∀ i,r.SourceStable (inputs i).source)
    (cs : R → Nat) (B : Nat) (hb : cs base ≤ B) (hi : ∀ i,(inputs i).eval cs ≤ B) :
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).counters cs r.p ≤ B+extractionTermSchemaBudget tm e ∧
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).counters cs r.q ≤ B+extractionTermSchemaBudget tm e ∧
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).counters cs r.r ≤ B+extractionTermSchemaBudget tm e := by
  obtain ⟨hx,hy,hz⟩ := formulaPrinter_counters_fields_bound (extractionTermSchema tm e first endpoint value)
    inputs base 0 backward r hpq hpr hqr hcp hcq hcr hsb hsi cs B hb hi
  have hsize := extractionTermSchema_size_bound tm e first endpoint value
  change fixedNodeCounters r _ cs r.p ≤ _ ∧ fixedNodeCounters r _ cs r.q ≤ _ ∧ fixedNodeCounters r _ cs r.r ≤ _
  exact ⟨by omega,by omega,by omega⟩

end ShiReversibleGenerator
