import ReversibleProgramTemplateSequence
import ReversibleLayerCounting
import ReversibleCnotEmission

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- Print one CNOT from runtime source/target addresses and count its actual quantum layer. -/
noncomputable def countedCopyProgramTemplate (source target count buf tmp : R) : CounterProgramTemplate R where
  Labels := GeneratorActionLabels (countedEmissionActions (cxAtoms source target) source count 1)
  finite := fun L f => by letI := f; infer_instance
  code := fun caller stop => actionCode (countedEmissionActions (cxAtoms source target) source count 1) caller buf tmp stop
  entry := fun stop => actionEntry (countedEmissionActions (cxAtoms source target) source count 1) stop
  exit := fun stop => actionExit (countedEmissionActions (cxAtoms source target) source count 1) stop
  ready := fun cs => cs buf=0 ∧ cs tmp=0
  steps := fun cs => actionSteps (countedEmissionActions (cxAtoms source target) source count 1) cs
  counters := fun cs => Function.update cs count (cs count+1)
  bytes := fun cs => emissionBytes (cxAtoms source target) cs

theorem countedCopyProgramTemplate_embeds (source target count buf tmp : R) :
    (countedCopyProgramTemplate source target count buf tmp).Embeds := by
  intro L caller stop l
  exact actionCode_embed _ caller buf tmp stop l

theorem countedCopyProgramTemplate_run (source target count buf tmp : R)
    (hsb : source ≠ buf) (hst : source ≠ tmp) (htb : target ≠ buf) (htt : target ≠ tmp)
    (hsc : source ≠ count) (hct : count ≠ tmp) (hcb : count ≠ buf) (hbt : buf ≠ tmp) :
    (countedCopyProgramTemplate source target count buf tmp).Runs := by
  intro L caller stop cs ys hr
  exact countedEmission_run (cxAtoms source target) source count buf tmp 1 caller stop
    (by simp [cxAtoms,EmissionAtom.Valid,hsb,hst,htb,htt]) hsc hst hct hcb hbt cs hr.1 hr.2 ys

theorem countedCopyProgramTemplate_bytes {wires : Nat} (source target count buf tmp : R)
    (cs : R → Nat) (i j : Fin wires) (hij : i ≠ j) (hi : cs source=i.val) (hj : cs target=j.val) :
    (countedCopyProgramTemplate source target count buf tmp).bytes cs=ShiBQP.encLayer [.cnot i j hij] := by
  simp [countedCopyProgramTemplate,cxAtoms,emissionBytes,EmissionAtom.bytes,encLayer_singleton,
    ShiBQP.encInstr,hi,hj,List.append_assoc]

theorem countedCopyProgramTemplate_steps (source target count buf tmp : R) (cs : R → Nat) :
    (countedCopyProgramTemplate source target count buf tmp).steps cs=10*cs source+10*cs target+16 := by
  simp [countedCopyProgramTemplate,countedEmissionActions,cxAtoms,actionSteps,GeneratorAction.steps,
    GeneratorAction.counters,GeneratorOperation.steps,AffineAtom.steps,EmissionAtom.steps,ShiBQP.encNat]
  omega

theorem countedCopyProgramTemplate_polynomial (source target count buf tmp : R) (bound : Polynomial Nat) :
    (countedCopyProgramTemplate source target count buf tmp).PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 20*bound+Polynomial.C 16,?_⟩
  intro n cs hb _
  rw [countedCopyProgramTemplate_steps]
  have hs := hb source
  have ht := hb target
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
