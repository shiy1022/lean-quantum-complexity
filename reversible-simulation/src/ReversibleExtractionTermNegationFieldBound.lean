import ReversibleExtractionTermNegationPrinter
import ReversiblePrinterFieldBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The last inverse-prefix negation resets all fields using only bounded base and size counters. -/
theorem extractionTermNegationPrinterTemplate_fields_bound (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (B : Nat) (hbase : cs 18 ≤ B) (hsize : cs 12 ≤ B) :
    (extractionTermNegationPrinterTemplate backward).counters cs 13 ≤ 2*B+1 ∧
    (extractionTermNegationPrinterTemplate backward).counters cs 14 ≤ 2*B+1 ∧
    (extractionTermNegationPrinterTemplate backward).counters cs 15 ≤ 2*B+1 := by
  let after := extractionTermNegationSetupTemplate.counters cs
  let t := symbolicAssignmentTemplate backward (.neg ⟨19,0⟩ ⟨21,0⟩ : SymbolicAssignment ExtractionTermRegister)
  have hf := FixedNodeTemplate.counters_fields t extractionTermNodeRegisters
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [t,symbolicAssignmentTemplate,FixedNodeTemplate.StableSources,extractionTermNodeRegisters]) after
  change t.counters extractionTermNodeRegisters after 13 ≤ 2*B+1 ∧
    t.counters extractionTermNodeRegisters after 14 ≤ 2*B+1 ∧
    t.counters extractionTermNodeRegisters after 15 ≤ 2*B+1
  change t.counters extractionTermNodeRegisters after 13=t.x.eval after ∧
    t.counters extractionTermNodeRegisters after 14=t.y.eval after ∧
    t.counters extractionTermNodeRegisters after 15=t.z.eval after at hf
  rw [hf.1,hf.2.1,hf.2.2]
  simp only [t,symbolicAssignmentTemplate,SymbolicWire.eval,after,extractionTermNegationSetupTemplate_counters]
  simp only [Function.update_self,Function.update_of_ne (by decide : (19 : ExtractionTermRegister) ≠ 21),Nat.add_zero]
  omega

end ShiReversibleGenerator
