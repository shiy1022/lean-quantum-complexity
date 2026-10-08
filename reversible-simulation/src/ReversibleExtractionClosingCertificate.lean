import ReversibleExtractionClosingPrinter
import ReversibleFormulaLayerCount

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem extractionClosingPrinterTemplate_count (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) (hp : r.count ≠ r.p) (hq : r.count ≠ r.q) (hr : r.count ≠ r.r)
    (cs : R → Nat) :
    (extractionClosingPrinterTemplate backward termNeg suffixRoot r).counters cs r.count=cs r.count+41 := by
  change fixedNodeCounters r _ cs r.count=_
  rw [fixedNodeCounters_count r _ hp hq hr]
  cases backward <;> simp [extractionClosingPrinterTemplates,extractionClosingAssignments,
    fixedNodeLayerCount,symbolicAssignmentTemplate,AssignmentEmissionKind.layers]

/-- Actual finite closing-node run, exact circuit bytes, exact layer count, and polynomial clock. -/
theorem extractionClosingPrinterTemplate_certificate (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) (hr : r.Valid)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hcp : r.count ≠ r.p) (hcq : r.count ≠ r.q) (hcr : r.count ≠ r.r)
    (ha : r.SourceStable termNeg) (hq : r.SourceStable suffixRoot) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q,cs q ≤ bound.eval n) →
      cs r.buf=0 → cs r.tmp=0 →
      ∀ (L : Type) (caller : L → CounterInstr R L) (stop : L) (ys : List Bool),
      let p := extractionClosingPrinterTemplate backward termNeg suffixRoot r
      let nodes := if backward then (extractionClosingAssignments termNeg suffixRoot).reverse
        else extractionClosingAssignments termNeg suffixRoot
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,
          (nodes.map (fun a => rawAssignmentPayload backward (a.eval cs))).flatten++ys⟩ ∧
      p.steps cs ≤ clock.eval n ∧ p.counters cs r.count=cs r.count+41 := by
  obtain ⟨clock,hclock⟩ := extractionClosingPrinterTemplate_polynomial backward termNeg suffixRoot r bound
  refine ⟨clock,?_⟩
  intro n cs hb hbuf htmp L caller stop ys
  dsimp only
  have hready : (extractionClosingPrinterTemplate backward termNeg suffixRoot r).ready cs := ⟨hbuf,htmp⟩
  have hrun := extractionClosingPrinterTemplate_run backward termNeg suffixRoot r hr ha hq L caller stop cs ys hready
  rw [extractionClosingPrinterTemplate_payload backward termNeg suffixRoot r hpq hpr hqr ha hq cs] at hrun
  exact ⟨hrun,hclock n cs hb hready,extractionClosingPrinterTemplate_count backward termNeg suffixRoot r hcp hcq hcr cs⟩

end ShiReversibleGenerator
