import ReversibleExtractionClosingFieldBound
import ReversibleExtractionClosingStep
import ReversibleExtractionTermSizeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionBoundClosingPrinterTemplate_fields_bound (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (B : Nat) (hbase : cs 18 ≤ B) (hend : cs 20 ≤ B) :
    let bound := B+(10+Fintype.card (Option (MachineSymbol tm))*7)+3
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 13 ≤ bound ∧
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 14 ≤ bound ∧
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 15 ≤ bound := by
  let after := (extractionClosingSetupTemplate tm).counters cs
  have hc := extractionSizeContribution_bound tm (cs 2) (cs 1)
  have ht : after 19 ≤ B+(10+Fintype.card (Option (MachineSymbol tm))*7)+3 := by
    simp only [after,extractionClosingSetupTemplate_counters,Function.update_of_ne (by decide : (19 : ExtractionTermRegister) ≠ 21),Function.update_self]
    omega
  have hs : after 21+3 ≤ B+(10+Fintype.card (Option (MachineSymbol tm))*7)+3 := by
    simp only [after,extractionClosingSetupTemplate_counters,Function.update_self]
    omega
  exact extractionClosingPrinterTemplate_fields_bound backward 19 21 extractionTermNodeRegisters
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable])
    (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]) after _ ht hs

theorem extractionClosingStepTemplate_fields_bound (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (B : Nat) (hbase : cs 18 ≤ B) (hend : cs 20 ≤ B) :
    let bound := B+(10+Fintype.card (Option (MachineSymbol tm))*7)+3
    (extractionClosingStepTemplate tm backward).counters cs 13 ≤ bound ∧
    (extractionClosingStepTemplate tm backward).counters cs 14 ≤ bound ∧
    (extractionClosingStepTemplate tm backward).counters cs 15 ≤ bound := by
  simpa only [extractionClosingStepTemplate,sequenceProgramTemplate,
    extractionClosingAdvanceTemplate_counters,Function.update_of_ne (by decide : (13 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (13 : ExtractionTermRegister) ≠ 21),Function.update_of_ne (by decide : (13 : ExtractionTermRegister) ≠ 20),
    Function.update_of_ne (by decide : (13 : ExtractionTermRegister) ≠ 19),Function.update_of_ne (by decide : (13 : ExtractionTermRegister) ≠ 18),
    Function.update_of_ne (by decide : (14 : ExtractionTermRegister) ≠ 2),Function.update_of_ne (by decide : (14 : ExtractionTermRegister) ≠ 21),
    Function.update_of_ne (by decide : (14 : ExtractionTermRegister) ≠ 20),Function.update_of_ne (by decide : (14 : ExtractionTermRegister) ≠ 19),
    Function.update_of_ne (by decide : (14 : ExtractionTermRegister) ≠ 18),Function.update_of_ne (by decide : (15 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (15 : ExtractionTermRegister) ≠ 21),Function.update_of_ne (by decide : (15 : ExtractionTermRegister) ≠ 20),
    Function.update_of_ne (by decide : (15 : ExtractionTermRegister) ≠ 19),Function.update_of_ne (by decide : (15 : ExtractionTermRegister) ≠ 18)] using
    extractionBoundClosingPrinterTemplate_fields_bound tm backward cs B hbase hend

end ShiReversibleGenerator
