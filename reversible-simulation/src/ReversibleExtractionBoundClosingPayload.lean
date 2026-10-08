import ReversibleExtractionBoundClosingPrinter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The fully bound finite printer emits exactly the original compiler's three closing nodes. -/
theorem extractionBoundClosingPrinterTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) (hend : 3 ≤ cs 20) :
    let term := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
      (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
    let nodes := [RawAssignment.neg (cs 20-3) (cs 20-2),
      .conj (cs 18+term.size) (cs 20-2) (cs 20-1),.neg (cs 20-1) (cs 20)]
    (extractionBoundClosingPrinterTemplate tm backward).bytes cs=
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  dsimp only
  let term := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
    (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
  let after := (extractionClosingSetupTemplate tm).counters cs
  have ha : after 19=cs 18+term.size := by
    simp only [after,extractionClosingSetupTemplate_counters,Function.update_of_ne (by decide : (19 : ExtractionTermRegister) ≠ 21),Function.update_self]
    rw [extractionSizeContribution_exact tm e (cs 0) (cs 2) (cs 1) hell]
    change cs 18+(term.size+4)-4=cs 18+term.size
    omega
  have hq : after 21=cs 20-3 := by simp [after,extractionClosingSetupTemplate_counters]
  have h1 : cs 20-3+1=cs 20-2 := by omega
  have h2 : cs 20-3+2=cs 20-1 := by omega
  have h3 : cs 20-3+3=cs 20 := by omega
  have h := extractionClosingPrinterTemplate_payload backward 19 21 extractionTermNodeRegisters
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable])
    (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]) after
  cases backward <;> simpa [extractionBoundClosingPrinterTemplate,sequenceProgramTemplate,
    extractionClosingSetupTemplate_bytes,after,extractionClosingAssignments,SymbolicAssignment.eval,
    SymbolicWire.eval,ha,hq,h1,h2,h3,term] using h

theorem extractionBoundClosingPrinterTemplate_count (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 16=cs 16+41 := by
  change (extractionClosingPrinterTemplate backward 19 21 extractionTermNodeRegisters).counters
    ((extractionClosingSetupTemplate tm).counters cs) extractionTermNodeRegisters.count=_
  rw [extractionClosingPrinterTemplate_count backward 19 21 extractionTermNodeRegisters
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])]
  simp [extractionTermNodeRegisters,extractionClosingSetupTemplate_counters,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

end ShiReversibleGenerator
