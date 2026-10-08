import ReversibleCounterAffineExitBounds
import ReversibleCleanupProgramTemplate
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R] [Fintype R]

/-- Shared registers retain raw length, total layers and scratch; the right summand is private. -/
abbrev RawLengthPhaseRegister (R : Type) := Fin 3 ⊕ R

noncomputable def rawLengthPhasePrivate : List (RawLengthPhaseRegister R) :=
  (Finset.univ : Finset R).toList.map Sum.inr

/-- Clear the whole private block, then copy the preserved length into its input register. -/
noncomputable def rawLengthPhaseLoader (input : R) : CounterProgramTemplate (RawLengthPhaseRegister R) :=
  sequenceProgramTemplate (cleanupProgramTemplate rawLengthPhasePrivate)
    (counterAffineCopyProgramTemplate (.inl 0) (.inr input) (.inl 2) 0 1 0)

theorem rawLengthPhaseLoader_embeds (input : R) : (rawLengthPhaseLoader input).Embeds :=
  sequenceProgramTemplate_embeds _ _ (cleanupProgramTemplate_embeds _)
    (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)

theorem rawLengthPhaseLoader_run (input : R) : (rawLengthPhaseLoader input).Runs := by
  apply sequenceProgramTemplate_run _ _ (cleanupProgramTemplate_embeds _) (cleanupProgramTemplate_run _)
  apply counterAffineCopyProgramTemplate_run <;> simp

theorem rawLengthPhaseLoader_ready (input : R) (cs : RawLengthPhaseRegister R → Nat) :
    (rawLengthPhaseLoader input).ready cs ↔ cs (.inl 2)=0 := by
  simp [rawLengthPhaseLoader,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupCounters_apply,rawLengthPhasePrivate]

theorem rawLengthPhaseLoader_private (input : R) (cs : RawLengthPhaseRegister R → Nat) :
    (fun r => (rawLengthPhaseLoader input).counters cs (.inr r))=
      Function.update (fun _ : R => 0) input (cs (.inl 0)) := by
  funext r
  simp [rawLengthPhaseLoader,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupCounters_apply,rawLengthPhasePrivate,Function.update_apply]

theorem rawLengthPhaseLoader_shared (input : R) (cs : RawLengthPhaseRegister R → Nat) (j : Fin 3) :
    (rawLengthPhaseLoader input).counters cs (.inl j)=cs (.inl j) := by
  simp [rawLengthPhaseLoader,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupCounters_apply,rawLengthPhasePrivate,Function.update_apply]

theorem rawLengthPhaseLoader_bytes (input : R) (cs : RawLengthPhaseRegister R → Nat) :
    (rawLengthPhaseLoader input).bytes cs=[] := by
  simp [rawLengthPhaseLoader,sequenceProgramTemplate,cleanupProgramTemplate,counterAffineCopyProgramTemplate]

theorem rawLengthPhaseLoader_resources (input : R) (bound : Polynomial Nat) :
    (rawLengthPhaseLoader input).CounterBound bound ∧ (rawLengthPhaseLoader input).PolynomiallyTimed bound := by
  refine ⟨⟨bound,?_⟩,sequenceProgramTemplate_polynomial _ _ bound bound
    (cleanupProgramTemplate_polynomial _ bound) ?_ (counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ bound)⟩
  · intro n cs hb q
    exact counterAffineUnitCopyProgramTemplate_budget (.inl 0) (.inr input) (.inl 2) 0 _ _
      (cleanupCounters_uniform_bound _ cs (bound.eval n) hb) q
  · intro n cs hb hr q
    exact cleanupCounters_uniform_bound _ cs (bound.eval n) hb q

end ShiReversibleGenerator
