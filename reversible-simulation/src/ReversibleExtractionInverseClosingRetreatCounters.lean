import ReversibleExtractionInverseClosingRetreat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The two real pointers retreat by the selected term's size plus its negation node. -/
theorem extractionInverseClosingRetreatTemplate_counters (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingRetreatTemplate tm).counters cs=
      let t := (extractionTermSizeProgramTemplate tm).counters cs
      Function.update (Function.update (Function.update t 18
        (t 18-(t 12-3))) 19 (t 19-(t 12-3))) 8 0 := by
  change (counterPairRetreatTemplate 18 19 8).counters
    ((counterAffineCopyProgramTemplate 12 8 7 0 1 3).counters
      ((extractionTermSizeProgramTemplate tm).counters cs))=_
  rw [counterPairRetreatTemplate_counters _ _ _ (by decide) (by decide) (by decide)]
  simp only [counterAffineCopyProgramTemplate,Nat.one_mul,Nat.zero_add,
    Function.update_self,Function.update_of_ne (by decide : (18 : ExtractionTermRegister) ≠ 8),
    Function.update_of_ne (by decide : (19 : ExtractionTermRegister) ≠ 8)]
  funext q
  by_cases h8 : q=8 <;> by_cases h18 : q=18 <;> by_cases h19 : q=19
  all_goals simp_all [Function.update_apply]

end ShiReversibleGenerator
