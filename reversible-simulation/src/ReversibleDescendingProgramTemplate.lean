import ReversibleContinuationLoopRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- A fixed finite control graph performs a runtime-counted traversal and returns to its caller. -/
noncomputable def descendingProgramTemplate (p : CounterProgramTemplate R) (remaining : R) :
    CounterProgramTemplate R where
  Labels := fun L => p.Labels (LoopContinuation L)
  finite := fun L f => by
    letI := f
    exact p.finite (LoopContinuation L) inferInstance
  code := continuationLoopCode p remaining
  entry := fun _ => p.exit (.inl ())
  exit := fun l => p.exit (.inr (.inr l))
  ready := fun cs => descendingTemplateReady p remaining (cs remaining) cs
  steps := fun cs => descendingTemplateSteps p remaining (cs remaining) cs
  counters := fun cs => Function.update (descendingTemplateCounters p remaining (cs remaining) cs) remaining 0
  bytes := fun cs => descendingTemplateBytes p remaining (cs remaining) cs

theorem descendingProgramTemplate_embeds (p : CounterProgramTemplate R) (remaining : R) (he : p.Embeds) :
    (descendingProgramTemplate p remaining).Embeds := by
  intro L caller stop l
  exact continuationLoopCode_embed p remaining he caller stop l

/-- Execution is derived from actual instruction runs, including loop tests and decrements. -/
theorem descendingProgramTemplate_run (p : CounterProgramTemplate R) (remaining : R)
    (he : p.Embeds) (hr : p.Runs) : (descendingProgramTemplate p remaining).Runs := by
  intro L caller stop cs ys hs
  let s : CounterCfg R (p.Labels (LoopContinuation L)) := ⟨none,cs,ys⟩
  have h := continuationDescendingTraversal_run p remaining he hr caller stop
    (fun k t => descendingTemplateReady p remaining k t.counters)
    (fun k t ht => ht.1) (fun k t ht => ht.2.1) (fun k t ht => ht.2.2)
    (cs remaining) s hs
  have hu : Function.update cs remaining (cs remaining) = cs := by
    funext q
    by_cases hq : q=remaining
    · subst q; simp
    · simp [hq]
  rw [descendingTemplateSteps_eq] at h
  simp only [withCounter] at h
  rw [descendingTemplateResult_counters,descendingTemplateResult_output] at h
  simpa only [descendingProgramTemplate,withCounter,s,hu] using h

end ShiReversibleGenerator
