import ReversibleRawLengthPhaseLoader
import ReversibleCountedComponentProgramTemplate
import ReversibleInjectedProgramTemplateBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- One phase loads the shared length, runs the actual raw printer, accumulates its count, and clears its private block. -/
noncomputable def rawLengthPhaseTemplate (p : CounterProgramTemplate R) (input localCount : R) :
    CounterProgramTemplate (RawLengthPhaseRegister R) :=
  sequenceProgramTemplate (rawLengthPhaseLoader input)
    (countedComponentProgramTemplate (injectProgramTemplate p Sum.inr input)
      (.inr localCount) (.inl 1) (.inl 2) rawLengthPhasePrivate)

theorem rawLengthPhaseTemplate_embeds (p : CounterProgramTemplate R) (input localCount : R) :
    (rawLengthPhaseTemplate p input localCount).Embeds :=
  sequenceProgramTemplate_embeds _ _ (rawLengthPhaseLoader_embeds _)
    (countedComponentProgramTemplate_embeds _ _ _ _ _ (injectProgramTemplate_embeds _ _ _))

theorem rawLengthPhaseTemplate_run (p : CounterProgramTemplate R) (input localCount : R)
    (he : p.Embeds) (hr : p.Runs) : (rawLengthPhaseTemplate p input localCount).Runs := by
  apply sequenceProgramTemplate_run _ _ (rawLengthPhaseLoader_embeds _) (rawLengthPhaseLoader_run _)
  apply countedComponentProgramTemplate_run _ _ _ _ _ (injectProgramTemplate_embeds _ _ _)
    (injectProgramTemplate_run _ _ (by intro a b h; exact Sum.inr.inj h) _ he hr)
  all_goals simp

theorem rawLengthPhaseTemplate_ready (p : CounterProgramTemplate R) (input localCount : R)
    (hp : ∀ n,p.ready (Function.update (fun _ : R => 0) input n))
    (cs : RawLengthPhaseRegister R → Nat) (htmp : cs (.inl 2)=0) :
    (rawLengthPhaseTemplate p input localCount).ready cs := by
  refine ⟨(rawLengthPhaseLoader_ready input cs).2 htmp,?_⟩
  apply (countedComponentProgramTemplate_ready _ _ _ _ _ _).2
  refine ⟨?_,?_⟩
  · change p.ready (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))
    rw [rawLengthPhaseLoader_private]
    exact hp _
  · change injectedTemplateCounters Sum.inr ((rawLengthPhaseLoader input).counters cs)
      (p.counters (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))) (.inl 2)=0
    rw [injectedTemplateCounters_outside _ _ _ _ (by intro r; simp),rawLengthPhaseLoader_shared]
    exact htmp

theorem rawLengthPhaseTemplate_bytes (p : CounterProgramTemplate R) (input localCount : R)
    (cs : RawLengthPhaseRegister R → Nat) :
    (rawLengthPhaseTemplate p input localCount).bytes cs=
      p.bytes (Function.update (fun _ : R => 0) input (cs (.inl 0))) := by
  change (countedComponentProgramTemplate (injectProgramTemplate p Sum.inr input)
    (.inr localCount) (.inl 1) (.inl 2) rawLengthPhasePrivate).bytes
      ((rawLengthPhaseLoader input).counters cs)++(rawLengthPhaseLoader input).bytes cs=_
  rw [countedComponentProgramTemplate_bytes,rawLengthPhaseLoader_bytes,List.append_nil]
  change p.bytes (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))=_
  rw [rawLengthPhaseLoader_private]

theorem rawLengthPhaseTemplate_count (p : CounterProgramTemplate R) (input localCount : R)
    (cs : RawLengthPhaseRegister R → Nat) :
    (rawLengthPhaseTemplate p input localCount).counters cs (.inl 1)=
      cs (.inl 1)+p.counters (Function.update (fun _ : R => 0) input (cs (.inl 0))) localCount := by
  change (countedComponentProgramTemplate (injectProgramTemplate p Sum.inr input)
    (.inr localCount) (.inl 1) (.inl 2) rawLengthPhasePrivate).counters
      ((rawLengthPhaseLoader input).counters cs) (.inl 1)=_
  rw [countedComponentProgramTemplate_count]
  · change (rawLengthPhaseLoader input).counters cs (.inl 1)+
      injectedTemplateCounters Sum.inr ((rawLengthPhaseLoader input).counters cs)
        (p.counters (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))) (.inr localCount)=_
    rw [injectedTemplateCounters_pull _ (by intro a b h; exact Sum.inr.inj h),
      rawLengthPhaseLoader_shared,rawLengthPhaseLoader_private]
  · simp [rawLengthPhasePrivate]
  · exact injectedTemplateCounters_outside _ _ _ _ (by intro r; simp)

theorem rawLengthPhaseTemplate_cleared (p : CounterProgramTemplate R) (input localCount : R)
    (cs : RawLengthPhaseRegister R → Nat) (r : R) :
    (rawLengthPhaseTemplate p input localCount).counters cs (.inr r)=0 := by
  apply countedComponentProgramTemplate_cleared
  simp [rawLengthPhasePrivate]

theorem rawLengthPhaseTemplate_shared (p : CounterProgramTemplate R) (input localCount : R)
    (cs : RawLengthPhaseRegister R → Nat) (j : Fin 3) (hj : j ≠ 1) :
    (rawLengthPhaseTemplate p input localCount).counters cs (.inl j)=cs (.inl j) := by
  change (countedComponentProgramTemplate (injectProgramTemplate p Sum.inr input)
    (.inr localCount) (.inl 1) (.inl 2) rawLengthPhasePrivate).counters
      ((rawLengthPhaseLoader input).counters cs) (.inl j)=_
  rw [countedComponentProgramTemplate_frame]
  · change injectedTemplateCounters Sum.inr ((rawLengthPhaseLoader input).counters cs)
      (p.counters (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))) (.inl j)=_
    rw [injectedTemplateCounters_outside _ _ _ _ (by intro r; simp)]
    exact rawLengthPhaseLoader_shared _ _ _
  · simp [rawLengthPhasePrivate]
  · simpa using hj

theorem rawLengthPhaseTemplate_resources (p : CounterProgramTemplate R) (input localCount : R)
    (bound : Polynomial Nat) (hb : p.CounterBound bound) (ht : p.PolynomiallyTimed bound) :
    (rawLengthPhaseTemplate p input localCount).CounterBound bound ∧
    (rawLengthPhaseTemplate p input localCount).PolynomiallyTimed bound := by
  obtain ⟨⟨middle,hm⟩,hl⟩ := rawLengthPhaseLoader_resources input bound
  have hi := injectProgramTemplate_budget p (Sum.inr : R → RawLengthPhaseRegister R) (by intro a b h; exact Sum.inr.inj h) input bound hb
  have ht' := injectProgramTemplate_polynomial p (Sum.inr : R → RawLengthPhaseRegister R) input bound ht
  have hload : ∀ n (cs : RawLengthPhaseRegister R → Nat),(∀ q,cs q ≤ bound.eval n) →
      ∀ q,(rawLengthPhaseLoader input).counters cs q ≤ bound.eval n := by
    intro n cs hc q
    cases q with
    | inl j => rw [rawLengthPhaseLoader_shared]; exact hc _
    | inr r =>
      have h := congrFun (rawLengthPhaseLoader_private input cs) r
      rw [h]
      simp only [Function.update_apply]
      split_ifs
      · exact hc _
      · exact Nat.zero_le _
  obtain ⟨⟨after,ha⟩,hc⟩ := countedComponentProgramTemplate_resources (injectProgramTemplate p Sum.inr input)
    (.inr localCount) (.inl 1) (.inl 2) rawLengthPhasePrivate bound hi ht'
  exact ⟨⟨after,fun n cs hs q => ha n _ (hload n cs hs) q⟩,
    sequenceProgramTemplate_polynomial _ _ bound bound hl (fun n cs hs _ => hload n cs hs) hc⟩

end ShiReversibleGenerator
