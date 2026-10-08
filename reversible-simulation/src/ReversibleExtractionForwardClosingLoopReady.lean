import ReversibleExtractionForwardClosingLoop
import ReversibleExtractionClosingStepFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionForwardClosingLoopTemplate_ready (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (hb : cs 17=0) :
    (extractionForwardClosingLoopTemplate tm).ready cs := by
  have h : ∀ k (t : ExtractionTermRegister → Nat),t 17=0 →
      descendingTemplateReady (extractionClosingStepTemplate tm false) 9 k t := by
    intro k
    induction k with
    | zero => intro t ht; trivial
    | succ k ih =>
      intro t ht
      let next := Function.update t 9 k
      have hn : next 17=0 := by simp [next,ht]
      have h9 := extractionClosingStepTemplate_frame tm false next 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have h17 := extractionClosingStepTemplate_frame tm false next 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      refine ⟨extractionClosingStepTemplate_ready tm false next hn,?_,ih _ (h17.trans hn)⟩
      simpa [next] using h9
  exact h (cs 9) cs hb

/-- The real loop count is exhausted and exactly41layers are counted for each actual closing iteration. -/
theorem extractionForwardClosingLoopTemplate_count (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardClosingLoopTemplate tm).counters cs 16=cs 16+41*cs 9 := by
  have h : ∀ k (t : ExtractionTermRegister → Nat),
      descendingTemplateCounters (extractionClosingStepTemplate tm false) 9 k t 16=t 16+41*k := by
    intro k
    induction k with
    | zero => intro t; simp [descendingTemplateCounters]
    | succ k ih =>
      intro t
      rw [descendingTemplateCounters,ih,extractionClosingStepTemplate_count]
      simp only [Nat.mul_succ,Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 9)]
      omega
  change Function.update (descendingTemplateCounters _ 9 (cs 9) cs) 9 0 16=_
  rw [Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 9),h]

theorem extractionForwardClosingLoopTemplate_remaining (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardClosingLoopTemplate tm).counters cs 9=0 := by
  simp [extractionForwardClosingLoopTemplate,descendingProgramTemplate]

end ShiReversibleGenerator
