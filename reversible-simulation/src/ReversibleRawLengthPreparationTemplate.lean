import ReversibleRawLengthPhaseLoader
import ReversibleInjectedProgramTemplateBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- Load preserved length and retain the actual raw program's metadata for final header computation. -/
noncomputable def rawLengthPreparationTemplate (p : CounterProgramTemplate R) (input : R) :
    CounterProgramTemplate (RawLengthPhaseRegister R) :=
  sequenceProgramTemplate (rawLengthPhaseLoader input) (injectProgramTemplate p Sum.inr input)

theorem rawLengthPreparationTemplate_embeds (p : CounterProgramTemplate R) (input : R) :
    (rawLengthPreparationTemplate p input).Embeds :=
  sequenceProgramTemplate_embeds _ _ (rawLengthPhaseLoader_embeds _) (injectProgramTemplate_embeds _ _ _)

theorem rawLengthPreparationTemplate_run (p : CounterProgramTemplate R) (input : R) (he : p.Embeds) (hr : p.Runs) :
    (rawLengthPreparationTemplate p input).Runs :=
  sequenceProgramTemplate_run _ _ (rawLengthPhaseLoader_embeds _) (rawLengthPhaseLoader_run _)
    (injectProgramTemplate_run _ _ (by intro a b h; exact Sum.inr.inj h) _ he hr)

theorem rawLengthPreparationTemplate_ready (p : CounterProgramTemplate R) (input : R)
    (hp : ∀ n,p.ready (Function.update (fun _ : R => 0) input n))
    (cs : RawLengthPhaseRegister R → Nat) (hs : cs (.inl 2)=0) :
    (rawLengthPreparationTemplate p input).ready cs := by
  refine ⟨(rawLengthPhaseLoader_ready input cs).2 hs,?_⟩
  change p.ready (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))
  rw [rawLengthPhaseLoader_private]
  exact hp _

theorem rawLengthPreparationTemplate_private (p : CounterProgramTemplate R) (input : R)
    (cs : RawLengthPhaseRegister R → Nat) (r : R) :
    (rawLengthPreparationTemplate p input).counters cs (.inr r)=
      p.counters (Function.update (fun _ : R => 0) input (cs (.inl 0))) r := by
  change injectedTemplateCounters Sum.inr ((rawLengthPhaseLoader input).counters cs)
    (p.counters (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))) (.inr r)=_
  rw [injectedTemplateCounters_pull _ (by intro a b h; exact Sum.inr.inj h),rawLengthPhaseLoader_private]

theorem rawLengthPreparationTemplate_shared (p : CounterProgramTemplate R) (input : R)
    (cs : RawLengthPhaseRegister R → Nat) (j : Fin 3) :
    (rawLengthPreparationTemplate p input).counters cs (.inl j)=cs (.inl j) := by
  change injectedTemplateCounters Sum.inr ((rawLengthPhaseLoader input).counters cs)
    (p.counters (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))) (.inl j)=_
  rw [injectedTemplateCounters_outside _ _ _ _ (by intro r; simp),rawLengthPhaseLoader_shared]

theorem rawLengthPreparationTemplate_bytes (p : CounterProgramTemplate R) (input : R)
    (cs : RawLengthPhaseRegister R → Nat) :
    (rawLengthPreparationTemplate p input).bytes cs=
      p.bytes (Function.update (fun _ : R => 0) input (cs (.inl 0))) := by
  change p.bytes (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))++(rawLengthPhaseLoader input).bytes cs=_
  rw [rawLengthPhaseLoader_bytes,List.append_nil,rawLengthPhaseLoader_private]

theorem rawLengthPreparationTemplate_resources (p : CounterProgramTemplate R) (input : R)
    (bound : Polynomial Nat) (hb : p.CounterBound bound) (ht : p.PolynomiallyTimed bound) :
    (rawLengthPreparationTemplate p input).CounterBound bound ∧
    (rawLengthPreparationTemplate p input).PolynomiallyTimed bound := by
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
  obtain ⟨after,ha⟩ := injectProgramTemplate_budget p (Sum.inr : R → RawLengthPhaseRegister R)
    (by intro a b h; exact Sum.inr.inj h) input bound hb
  exact ⟨⟨after,fun n cs hc q => ha n _ (hload n cs hc) q⟩,
    sequenceProgramTemplate_polynomial _ _ bound bound (rawLengthPhaseLoader_resources input bound).2
      (fun n cs hc _ => hload n cs hc) (injectProgramTemplate_polynomial _ _ _ _ ht)⟩

end ShiReversibleGenerator
