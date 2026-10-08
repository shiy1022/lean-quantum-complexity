import ReversibleFamilyHeader
import ReversibleGuardedProgramTemplate
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- The established family header is a finite continuation template, emitted after the layer payload. -/
noncomputable def familyHeaderProgramTemplate (anc out depth buf tmp : R) : CounterProgramTemplate R where
  Labels := EmissionLabels (familyHeaderAtoms anc out depth)
  finite := fun L fl => by letI := fl; infer_instance
  code := fun caller stop => emissionCode (familyHeaderAtoms anc out depth) caller buf tmp stop
  entry := emissionEntry (familyHeaderAtoms anc out depth)
  exit := emissionExit (familyHeaderAtoms anc out depth)
  ready := fun cs => cs buf=0 ∧ cs tmp=0
  steps := emissionSteps (familyHeaderAtoms anc out depth)
  counters := id
  bytes := emissionBytes (familyHeaderAtoms anc out depth)

theorem familyHeaderProgramTemplate_embeds (anc out depth buf tmp : R) :
    (familyHeaderProgramTemplate anc out depth buf tmp).Embeds := by
  intro L caller stop l
  simp only [familyHeaderProgramTemplate,familyHeaderAtoms,emissionCode,emissionExit,
    EmissionAtom.code_embed]
  cases caller l <;> rfl

theorem familyHeaderProgramTemplate_run (anc out depth buf tmp : R)
    (ha : anc ≠ buf ∧ anc ≠ tmp) (ho : out ≠ buf ∧ out ≠ tmp)
    (hd : depth ≠ buf ∧ depth ≠ tmp) (hbt : buf ≠ tmp) :
    (familyHeaderProgramTemplate anc out depth buf tmp).Runs := by
  intro L caller stop cs ys hr
  exact emissionCode_run _ caller buf tmp stop
    (familyHeader_valid _ _ _ _ _ ha ho hd) hbt cs hr.1 hr.2 ys

theorem familyHeaderProgramTemplate_bytes (anc out depth buf tmp : R) (cs : R → Nat) :
    (familyHeaderProgramTemplate anc out depth buf tmp).bytes cs=
      ShiBQP.encNat (cs anc)++ShiBQP.encNat (cs out)++ShiBQP.encNat (cs depth) :=
  familyHeader_bytes _ _ _ _

theorem familyHeaderProgramTemplate_resources (anc out depth buf tmp : R) (bound : Polynomial Nat) :
    (familyHeaderProgramTemplate anc out depth buf tmp).CounterBound bound ∧
    (familyHeaderProgramTemplate anc out depth buf tmp).PolynomiallyTimed bound := by
  refine ⟨⟨bound,fun n cs hb q => hb q⟩,Polynomial.C 30*bound+Polynomial.C 12,?_⟩
  intro n cs hb hr
  have ha := hb anc
  have ho := hb out
  have hd := hb depth
  simp only [familyHeaderProgramTemplate,familyHeaderAtoms,emissionSteps,EmissionAtom.steps,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
