import ReversibleCountedComponentProgramTemplate
import ReversibleInjectedProgramTemplateBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- The first two ambient registers hold total layers and administrative scratch. -/
abbrev CountedPrivateRegister (R : Type) := Fin 2 ⊕ R

noncomputable def countedPrivateComponent (p : CounterProgramTemplate R) (branch localCount : R) :
    CounterProgramTemplate (CountedPrivateRegister R) :=
  countedComponentProgramTemplate (injectProgramTemplate p Sum.inr branch)
    (.inr localCount) (.inl 0) (.inl 1) ((Finset.univ : Finset R).toList.map Sum.inr)

theorem countedPrivateComponent_embeds (p : CounterProgramTemplate R) (branch localCount : R) :
    (countedPrivateComponent p branch localCount).Embeds :=
  countedComponentProgramTemplate_embeds _ _ _ _ _ (injectProgramTemplate_embeds _ _ _)

theorem countedPrivateComponent_run (p : CounterProgramTemplate R) (branch localCount : R)
    (he : p.Embeds) (hr : p.Runs) : (countedPrivateComponent p branch localCount).Runs := by
  apply countedComponentProgramTemplate_run _ _ _ _ _ (injectProgramTemplate_embeds _ _ _)
    (injectProgramTemplate_run _ _ (by intro a b h; exact Sum.inr.inj h) _ he hr)
  all_goals simp

theorem countedPrivateComponent_ready (p : CounterProgramTemplate R) (branch localCount : R)
    (cs : CountedPrivateRegister R → Nat) :
    (countedPrivateComponent p branch localCount).ready cs ↔
      p.ready (fun r => cs (.inr r)) ∧ cs (.inl 1)=0 := by
  rw [countedPrivateComponent,countedComponentProgramTemplate_ready]
  change p.ready (fun r => cs (.inr r)) ∧
    injectedTemplateCounters Sum.inr cs (p.counters (fun r => cs (.inr r))) (.inl 1)=0 ↔ _
  rw [injectedTemplateCounters_outside _ _ _ _ (by intro r; simp)]

theorem countedPrivateComponent_bytes (p : CounterProgramTemplate R) (branch localCount : R)
    (cs : CountedPrivateRegister R → Nat) :
    (countedPrivateComponent p branch localCount).bytes cs=p.bytes (fun r => cs (.inr r)) :=
  countedComponentProgramTemplate_bytes _ _ _ _ _ _

theorem countedPrivateComponent_count (p : CounterProgramTemplate R) (branch localCount : R)
    (cs : CountedPrivateRegister R → Nat) :
    (countedPrivateComponent p branch localCount).counters cs (.inl 0)=
      cs (.inl 0)+p.counters (fun r => cs (.inr r)) localCount := by
  rw [countedPrivateComponent,countedComponentProgramTemplate_count]
  · change cs (.inl 0)+injectedTemplateCounters Sum.inr cs
      (p.counters (fun r => cs (.inr r))) (.inr localCount)=_
    rw [injectedTemplateCounters_pull _ (by intro a b h; exact Sum.inr.inj h)]
  · simp
  · exact injectedTemplateCounters_outside _ _ _ _ (by intro r; simp)

theorem countedPrivateComponent_cleared (p : CounterProgramTemplate R) (branch localCount : R)
    (cs : CountedPrivateRegister R → Nat) (r : R) :
    (countedPrivateComponent p branch localCount).counters cs (.inr r)=0 := by
  apply countedComponentProgramTemplate_cleared
  simp

theorem countedPrivateComponent_scratch (p : CounterProgramTemplate R) (branch localCount : R)
    (cs : CountedPrivateRegister R → Nat) :
    (countedPrivateComponent p branch localCount).counters cs (.inl 1)=cs (.inl 1) := by
  rw [countedPrivateComponent,countedComponentProgramTemplate_frame]
  · exact injectedTemplateCounters_outside _ _ _ _ (by intro r; simp)
  · simp
  · simp

theorem countedPrivateComponent_resources (p : CounterProgramTemplate R) (branch localCount : R)
    (bound : Polynomial Nat) (hb : p.CounterBound bound) (ht : p.PolynomiallyTimed bound) :
    (countedPrivateComponent p branch localCount).CounterBound bound ∧
    (countedPrivateComponent p branch localCount).PolynomiallyTimed bound :=
  countedComponentProgramTemplate_resources _ _ _ _ _ bound
    (injectProgramTemplate_budget _ _ (by intro a b h; exact Sum.inr.inj h) _ _ hb)
    (injectProgramTemplate_polynomial _ _ _ _ ht)

end ShiReversibleGenerator
