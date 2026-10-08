import ReversibleFixedNodeProgramTemplate
import ReversibleFormulaSources
import ReversibleExtractionDisjoinPasses

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]
open ShiReversibleFormula

/-- Three actual raw closing nodes, from the term-negation address and the suffix root. -/
def extractionClosingAssignments (termNeg suffixRoot : R) : List (SymbolicAssignment R) :=
  [.neg ⟨suffixRoot,0⟩ ⟨suffixRoot,1⟩,
    .conj ⟨termNeg,0⟩ ⟨suffixRoot,1⟩ ⟨suffixRoot,2⟩,
    .neg ⟨suffixRoot,2⟩ ⟨suffixRoot,3⟩]

def extractionClosingPrinterTemplates (backward : Bool) (termNeg suffixRoot : R) : List (FixedNodeTemplate R) :=
  let ts := (extractionClosingAssignments termNeg suffixRoot).map (symbolicAssignmentTemplate backward)
  if backward then ts else ts.reverse

noncomputable def extractionClosingPrinterTemplate (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) : CounterProgramTemplate R :=
  fixedNodeProgramTemplate r (extractionClosingPrinterTemplates backward termNeg suffixRoot)

theorem extractionClosingPrinterTemplate_embeds (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) : (extractionClosingPrinterTemplate backward termNeg suffixRoot r).Embeds :=
  fixedNodeProgramTemplate_embeds _ _

theorem extractionClosingPrinterTemplate_run (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) (hr : r.Valid) (ha : r.SourceStable termNeg) (hq : r.SourceStable suffixRoot) :
    (extractionClosingPrinterTemplate backward termNeg suffixRoot r).Runs := by
  apply fixedNodeProgramTemplate_run _ _ hr
  intro t ht
  have ht' : t ∈ (extractionClosingAssignments termNeg suffixRoot).map (symbolicAssignmentTemplate backward) := by
    cases backward <;> simpa [extractionClosingPrinterTemplates] using ht
  obtain ⟨a,ha',rfl⟩ := List.mem_map.mp ht'
  simp only [extractionClosingAssignments,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ha'
  rcases ha' with rfl | rfl | rfl
  all_goals simp_all [symbolicAssignmentTemplate,FixedNodeTemplate.ops,nodeFieldOperations,
    GeneratorOperation.Valid,AffineAtom.Valid,NodePrinterRegisters.Valid,NodePrinterRegisters.SourceStable]

theorem extractionClosingPrinterTemplate_polynomial (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) (bound : Polynomial Nat) :
    (extractionClosingPrinterTemplate backward termNeg suffixRoot r).PolynomiallyTimed bound :=
  fixedNodeProgramTemplate_polynomial _ _ bound

/-- Exact forward or inverse closing-node payload, printed by the actual finite three-node program. -/
theorem extractionClosingPrinterTemplate_payload (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (ha : r.SourceStable termNeg) (hq : r.SourceStable suffixRoot) (cs : R → Nat) :
    (extractionClosingPrinterTemplate backward termNeg suffixRoot r).bytes cs=
      ((if backward then (extractionClosingAssignments termNeg suffixRoot).reverse
        else extractionClosingAssignments termNeg suffixRoot).map
        (fun a => rawAssignmentPayload backward (a.eval cs))).flatten := by
  have hs : ∀ t ∈ extractionClosingPrinterTemplates backward termNeg suffixRoot,t.StableSources r := by
    intro t ht
    have ht' : t ∈ (extractionClosingAssignments termNeg suffixRoot).map (symbolicAssignmentTemplate backward) := by
      cases backward <;> simpa [extractionClosingPrinterTemplates] using ht
    obtain ⟨a,ha',rfl⟩ := List.mem_map.mp ht'
    simp only [extractionClosingAssignments,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ha'
    rcases ha' with rfl | rfl | rfl
    all_goals simp_all [symbolicAssignmentTemplate,FixedNodeTemplate.StableSources,NodePrinterRegisters.SourceStable]
  change fixedNodeBytes r _ cs=_
  rw [fixedNodeBytes_payloads r _ hpq hpr hqr hs]
  cases backward <;> simp [extractionClosingPrinterTemplates,List.map_map,
    symbolicAssignmentTemplate_payload,Function.comp_def]

end ShiReversibleGenerator
