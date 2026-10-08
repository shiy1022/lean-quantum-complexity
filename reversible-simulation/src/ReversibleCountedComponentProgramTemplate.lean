import ReversibleCounterAffineExitBounds
import ReversibleCleanupProgramTemplate
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- Emit one component, add its actual layer count, and clear its private register block. -/
noncomputable def countedComponentProgramTemplate (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) : CounterProgramTemplate R :=
  sequenceProgramTemplate p (sequenceProgramTemplate
    (counterAffineAccumulationProgramTemplate ⟨localCount,total,0,1⟩ tmp)
    (cleanupProgramTemplate clear))

theorem countedComponentProgramTemplate_embeds (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (he : p.Embeds) :
    (countedComponentProgramTemplate p localCount total tmp clear).Embeds :=
  sequenceProgramTemplate_embeds _ _ he (sequenceProgramTemplate_embeds _ _
    (counterAffineAccumulationProgramTemplate_embeds _ _) (cleanupProgramTemplate_embeds _))

theorem countedComponentProgramTemplate_run (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (he : p.Embeds) (hr : p.Runs)
    (hs : localCount ≠ total) (ht : localCount ≠ tmp) (hx : total ≠ tmp) :
    (countedComponentProgramTemplate p localCount total tmp clear).Runs := by
  apply sequenceProgramTemplate_run _ _ he hr
  apply sequenceProgramTemplate_run _ _ (counterAffineAccumulationProgramTemplate_embeds _ _)
    (counterAffineAccumulationProgramTemplate_run _ _ ?_) (cleanupProgramTemplate_run _)
  exact ⟨hs,ht,hx⟩

theorem countedComponentProgramTemplate_ready (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (cs : R → Nat) :
    (countedComponentProgramTemplate p localCount total tmp clear).ready cs ↔
      p.ready cs ∧ p.counters cs tmp=0 := by
  simp [countedComponentProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineAccumulationProgramTemplate]

theorem countedComponentProgramTemplate_bytes (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (cs : R → Nat) :
    (countedComponentProgramTemplate p localCount total tmp clear).bytes cs=p.bytes cs := by
  simp [countedComponentProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineAccumulationProgramTemplate]

theorem countedComponentProgramTemplate_count (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (cs : R → Nat) (hc : total ∉ clear)
    (hf : p.counters cs total=cs total) :
    (countedComponentProgramTemplate p localCount total tmp clear).counters cs total=
      cs total+p.counters cs localCount := by
  simp [countedComponentProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    cleanupCounters_apply,hc,counterAffineAccumulationProgramTemplate,AffineAtom.apply,hf]

theorem countedComponentProgramTemplate_frame (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (cs : R → Nat) (q : R)
    (hc : q ∉ clear) (ht : q ≠ total) :
    (countedComponentProgramTemplate p localCount total tmp clear).counters cs q=p.counters cs q := by
  simp [countedComponentProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    cleanupCounters_apply,hc,counterAffineAccumulationProgramTemplate,AffineAtom.apply,ht]

theorem countedComponentProgramTemplate_cleared (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (cs : R → Nat) (q : R) (hc : q ∈ clear) :
    (countedComponentProgramTemplate p localCount total tmp clear).counters cs q=0 := by
  simp [countedComponentProgramTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    cleanupCounters_apply,hc]

theorem countedComponentProgramTemplate_resources (p : CounterProgramTemplate R)
    (localCount total tmp : R) (clear : List R) (bound : Polynomial Nat)
    (hb : p.CounterBound bound) (ht : p.PolynomiallyTimed bound) :
    (countedComponentProgramTemplate p localCount total tmp clear).CounterBound bound ∧
    (countedComponentProgramTemplate p localCount total tmp clear).PolynomiallyTimed bound := by
  obtain ⟨middle,hm⟩ := hb
  let after : Polynomial Nat := Polynomial.C 2*middle
  have ha : ∀ n (cs : R → Nat),(∀ q,cs q ≤ middle.eval n) →
      ∀ q,(counterAffineAccumulationProgramTemplate ⟨localCount,total,0,1⟩ tmp).counters cs q ≤ after.eval n := by
    intro n cs hc q
    simpa only [after,Polynomial.eval_mul,Polynomial.eval_C] using
      counterAffineUnitAccumulationProgramTemplate_budget localCount total tmp cs (middle.eval n) hc q
  refine ⟨⟨after,?_⟩,sequenceProgramTemplate_polynomial _ _ bound middle ht
    (fun n cs hc _ => hm n cs hc) ?_⟩
  · intro n cs hc q
    exact cleanupCounters_uniform_bound clear _ _ (ha n _ (hm n cs hc)) q
  · exact sequenceProgramTemplate_polynomial _ _ middle after
      (counterAffineAccumulationProgramTemplate_polynomial _ _ middle)
      (fun n cs hc _ => ha n cs hc) (cleanupProgramTemplate_polynomial _ after)

end ShiReversibleGenerator
