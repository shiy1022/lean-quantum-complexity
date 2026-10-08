import ReversibleExtractionClosingPrinter
import ReversiblePrinterFieldBounds

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- Closing printer fields depend only on the real term and suffix pointers, not on old field values. -/
theorem extractionClosingPrinterTemplate_fields_bound (backward : Bool) (termNeg suffixRoot : R)
    (r : NodePrinterRegisters R) (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hcp : r.count ≠ r.p) (hcq : r.count ≠ r.q) (hcr : r.count ≠ r.r)
    (ha : r.SourceStable termNeg) (hq : r.SourceStable suffixRoot) (cs : R → Nat) (B : Nat)
    (hterm : cs termNeg ≤ B) (hsuffix : cs suffixRoot+3 ≤ B) :
    (extractionClosingPrinterTemplate backward termNeg suffixRoot r).counters cs r.p ≤ B ∧
    (extractionClosingPrinterTemplate backward termNeg suffixRoot r).counters cs r.q ≤ B ∧
    (extractionClosingPrinterTemplate backward termNeg suffixRoot r).counters cs r.r ≤ B := by
  have member : ∀ t ∈ extractionClosingPrinterTemplates backward termNeg suffixRoot,
      ∃ a ∈ extractionClosingAssignments termNeg suffixRoot,t=symbolicAssignmentTemplate backward a := by
    intro t ht
    have hm : t ∈ (extractionClosingAssignments termNeg suffixRoot).map (symbolicAssignmentTemplate backward) := by
      cases backward <;> simpa [extractionClosingPrinterTemplates] using ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact ⟨a,ha,rfl⟩
  apply fixedNodeCounters_fields_bound r _ hpq hpr hqr hcp hcq hcr
  · intro t ht
    obtain ⟨a,hm,rfl⟩ := member t ht
    simp only [extractionClosingAssignments,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals simp_all [symbolicAssignmentTemplate,FixedNodeTemplate.StableSources,NodePrinterRegisters.SourceStable]
  · cases backward <;> simp [extractionClosingPrinterTemplates,extractionClosingAssignments]
  · intro t ht
    obtain ⟨a,hm,rfl⟩ := member t ht
    simp only [extractionClosingAssignments,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals simp only [symbolicAssignmentTemplate,SymbolicWire.eval]
    all_goals omega

end ShiReversibleGenerator
