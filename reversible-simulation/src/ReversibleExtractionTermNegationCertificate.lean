import ReversibleExtractionTermNegationPrinter
import ReversibleFormulaLayerCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula

theorem extractionTermNegationPrinterTemplate_ready (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (h7 : cs 7=0) (h17 : cs 17=0) :
    (extractionTermNegationPrinterTemplate backward).ready cs := by
  refine ⟨extractionTermNegationSetupTemplate_ready cs h7,?_⟩
  change extractionTermNegationSetupTemplate.counters cs 17=0 ∧
    extractionTermNegationSetupTemplate.counters cs 7=0
  rw [extractionTermNegationSetupTemplate_counters]
  simpa using And.intro h17 h7

/-- The negation node uses the computed term root and its consecutive fresh wire. -/
theorem extractionTermNegationPrinterTemplate_payload (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionTermNegationPrinterTemplate backward).bytes cs=
      rawAssignmentPayload backward (.neg (cs 18+cs 12-5) (cs 18+cs 12-5+1)) := by
  let after := extractionTermNegationSetupTemplate.counters cs
  have hs : ∀ t ∈ [symbolicAssignmentTemplate backward
      (.neg ⟨19,0⟩ ⟨21,0⟩ : SymbolicAssignment ExtractionTermRegister)],
      t.StableSources extractionTermNodeRegisters := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [symbolicAssignmentTemplate,FixedNodeTemplate.StableSources,
      extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]
  have h := fixedNodeBytes_payloads extractionTermNodeRegisters
    [symbolicAssignmentTemplate backward (.neg ⟨19,0⟩ ⟨21,0⟩)]
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters]) hs after
  simpa [extractionTermNegationPrinterTemplate,sequenceProgramTemplate,
    extractionTermNegationSetupTemplate_bytes,fixedNodeProgramTemplate,
    symbolicAssignmentTemplate_payload,SymbolicAssignment.eval,SymbolicWire.eval,
    after,extractionTermNegationSetupTemplate_counters] using h

theorem extractionTermNegationPrinterTemplate_count (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionTermNegationPrinterTemplate backward).counters cs 16=cs 16+2 := by
  change fixedNodeCounters extractionTermNodeRegisters _
    (extractionTermNegationSetupTemplate.counters cs) extractionTermNodeRegisters.count=_
  rw [fixedNodeCounters_count _ _ (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])]
  cases backward <;> simp [extractionTermNodeRegisters,extractionTermNegationSetupTemplate_counters,
    fixedNodeLayerCount,symbolicAssignmentTemplate,AssignmentEmissionKind.layers]

end ShiReversibleGenerator
