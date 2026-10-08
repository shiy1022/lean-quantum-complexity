import ReversibleOutputCopyStepPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

noncomputable def outputCopyLoopTemplate : CounterProgramTemplate OutputCopyRegister :=
  descendingProgramTemplate outputCopyStepTemplate 6

theorem outputCopyLoopTemplate_embeds : outputCopyLoopTemplate.Embeds :=
  descendingProgramTemplate_embeds _ _ outputCopyStepTemplate_embeds

theorem outputCopyLoopTemplate_run : outputCopyLoopTemplate.Runs :=
  descendingProgramTemplate_run _ _ outputCopyStepTemplate_embeds outputCopyStepTemplate_run

theorem outputCopyLoopTemplate_ready (cs : OutputCopyRegister → Nat) (hb : cs 3=0) (ht : cs 4=0) :
    outputCopyLoopTemplate.ready cs := by
  suffices h : ∀ k cs,cs 3=0 → cs 4=0 → descendingTemplateReady outputCopyStepTemplate 6 k cs by
    exact h _ _ hb ht
  intro k
  induction k with
  | zero => intro cs hb ht; trivial
  | succ k ih =>
    intro cs hb ht
    have hr : outputCopyStepTemplate.ready (Function.update cs 6 k) := by
      rw [outputCopyStepTemplate_ready]
      simpa using And.intro hb ht
    refine ⟨hr,?_,?_⟩
    · rw [outputCopyStepTemplate_remaining_frame]
      simp
    · have hnext := outputCopyStepTemplate_ready_preserved (Function.update cs 6 k) hr
      rw [outputCopyStepTemplate_ready] at hnext
      exact ih _ hnext.1 hnext.2

/-- Every actual iteration retreats the two pointers and adds exactly one layer. -/
theorem outputCopyLoopTemplate_pointer_count_result (cs : OutputCopyRegister → Nat) :
    outputCopyLoopTemplate.counters cs 0=cs 0-cs 6*cs 5 ∧
      outputCopyLoopTemplate.counters cs 1=cs 1-cs 6 ∧
      outputCopyLoopTemplate.counters cs 2=cs 2+cs 6 ∧
      outputCopyLoopTemplate.counters cs 5=cs 5 ∧ outputCopyLoopTemplate.counters cs 6=0 := by
  have h : ∀ k (t : OutputCopyRegister → Nat),
      descendingTemplateCounters outputCopyStepTemplate 6 k t 0=t 0-k*t 5 ∧
      descendingTemplateCounters outputCopyStepTemplate 6 k t 1=t 1-k ∧
      descendingTemplateCounters outputCopyStepTemplate 6 k t 2=t 2+k ∧
      descendingTemplateCounters outputCopyStepTemplate 6 k t 5=t 5 := by
    intro k
    induction k with
    | zero => intro t; simp [descendingTemplateCounters]
    | succ k ih =>
        intro t
        rw [descendingTemplateCounters]
        obtain ⟨h0,h1,h2,h5⟩ := ih (outputCopyStepTemplate.counters (Function.update t 6 k))
        rw [h0,h1,h2,h5,outputCopyStepTemplate_counters]
        simp [Nat.succ_mul,Nat.sub_sub,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  obtain ⟨h0,h1,h2,h5⟩ := h (cs 6) cs
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [outputCopyLoopTemplate,descendingProgramTemplate,
      Function.update_of_ne (by decide : (0 : OutputCopyRegister) ≠ 6)] using h0
  · simpa only [outputCopyLoopTemplate,descendingProgramTemplate,
      Function.update_of_ne (by decide : (1 : OutputCopyRegister) ≠ 6)] using h1
  · simpa only [outputCopyLoopTemplate,descendingProgramTemplate,
      Function.update_of_ne (by decide : (2 : OutputCopyRegister) ≠ 6)] using h2
  · simpa only [outputCopyLoopTemplate,descendingProgramTemplate,
      Function.update_of_ne (by decide : (5 : OutputCopyRegister) ≠ 6)] using h5
  · simp only [outputCopyLoopTemplate,descendingProgramTemplate,Function.update_self]

end ShiReversibleGenerator
