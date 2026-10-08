import ReversibleTickStackSetupInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

theorem descendingProgramTemplate_result_counters (p : CounterProgramTemplate R) (remaining : R)
    (cs : R → Nat) (ys : List Bool) (pc : Option L) :
    (descendingProgramTemplate p remaining).counters cs =
      Function.update (descendingResult (templateDescendingBody p remaining) (cs remaining)
        (⟨pc,cs,ys⟩ : CounterCfg R L)).counters remaining 0 := by
  rw [descendingTemplateResult_counters]
  rfl

theorem CounterBudget.cleanup {cs : R → Nat} {count : R} {bound : Nat}
    (h : CounterBudget cs count bound) (clear : List R) : CounterBudget (cleanupCounters clear cs) count bound := by
  intro q hq
  rw [cleanupCounters_apply]
  split
  · exact Nat.zero_le _
  · exact h q hq

end ShiReversibleGenerator
