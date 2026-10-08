import ReversibleOutputCopyStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- One real stride subtraction and one target decrement; unused registers are framed. -/
theorem outputCopyRetreatTemplate_counters (cs : OutputCopyRegister → Nat) :
    outputCopyRetreatTemplate.counters cs=
      Function.update (Function.update (Function.update (Function.update cs 0 (cs 0-cs 5))
        8 (cs 8-cs 5)) 7 0) 1 (cs 1-1) := by
  change (decrementProgramTemplate (1 : OutputCopyRegister)).counters
    ((counterPairRetreatTemplate (0 : OutputCopyRegister) 8 7).counters
      ((counterAffineCopyProgramTemplate (5 : OutputCopyRegister) 7 4 0 1 0).counters cs))=_
  rw [counterPairRetreatTemplate_counters _ _ _ (by decide) (by decide) (by decide)]
  funext q
  fin_cases q <;> simp [counterAffineCopyProgramTemplate,decrementProgramTemplate]

theorem outputCopyStepTemplate_counters (cs : OutputCopyRegister → Nat) :
    outputCopyStepTemplate.counters cs=
      Function.update (Function.update (Function.update (Function.update (Function.update cs 2 (cs 2+1))
        0 (cs 0-cs 5)) 8 (cs 8-cs 5)) 7 0) 1 (cs 1-1) := by
  change outputCopyRetreatTemplate.counters ((countedCopyProgramTemplate (0 : OutputCopyRegister) 1 2 3 4).counters cs)=_
  rw [outputCopyRetreatTemplate_counters]
  simp [countedCopyProgramTemplate]

theorem outputCopyStepTemplate_ready (cs : OutputCopyRegister → Nat) :
    outputCopyStepTemplate.ready cs ↔ cs 3=0 ∧ cs 4=0 := by
  change ((cs 3=0 ∧ cs 4=0) ∧ _) ↔ _
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_,?_,trivial⟩
    · simpa [countedCopyProgramTemplate,counterAffineCopyProgramTemplate] using h.2
    · exact counterPairRetreatTemplate_ready _ _ _ (by decide) (by decide) _

theorem outputCopyStepTemplate_ready_preserved (cs : OutputCopyRegister → Nat)
    (hr : outputCopyStepTemplate.ready cs) : outputCopyStepTemplate.ready (outputCopyStepTemplate.counters cs) := by
  rw [outputCopyStepTemplate_ready] at hr ⊢
  rw [outputCopyStepTemplate_counters]
  simpa using hr

theorem outputCopyStepTemplate_remaining_frame (cs : OutputCopyRegister → Nat) :
    outputCopyStepTemplate.counters cs 6=cs 6 := by
  rw [outputCopyStepTemplate_counters]
  simp

end ShiReversibleGenerator
