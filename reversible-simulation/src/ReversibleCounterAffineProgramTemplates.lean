import ReversibleTickForestCircuitCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- A finite runtime affine copy replaces its target and preserves its source. -/
noncomputable def counterAffineCopyProgramTemplate (source target tmp : R) (positive coefficient negative : Nat) : CounterProgramTemplate R where
  Labels := AddressBindingLabels positive coefficient negative
  finite := fun L f => by letI := f; infer_instance
  code := fun caller stop => addressBindingCode caller source target tmp positive coefficient negative stop
  entry := fun _ => .inl 0
  exit := fun l => .inr (.inr (.inr (.inr l)))
  ready := fun cs => cs tmp=0
  steps := fun cs => (2*cs target+1)+(coefficient*(7*cs source+2)+positive)+negative
  counters := fun cs => Function.update cs target (coefficient*cs source+positive-negative)
  bytes := fun _ => []

theorem counterAffineCopyProgramTemplate_embeds (source target tmp : R) (positive coefficient negative : Nat) :
    (counterAffineCopyProgramTemplate source target tmp positive coefficient negative).Embeds := by
  intro L caller stop l
  exact addressBindingCode_embed caller source target tmp positive coefficient negative stop l

theorem counterAffineCopyProgramTemplate_run (source target tmp : R) (positive coefficient negative : Nat)
    (hst : source ≠ target) (hsx : source ≠ tmp) (htx : target ≠ tmp) :
    (counterAffineCopyProgramTemplate source target tmp positive coefficient negative).Runs := by
  intro L caller stop cs ys hs
  exact addressBindingCode_run caller source target tmp positive coefficient negative stop hst hsx htx cs hs ys

theorem counterAffineCopyProgramTemplate_polynomial (source target tmp : R) (positive coefficient negative : Nat)
    (bound : Polynomial Nat) : (counterAffineCopyProgramTemplate source target tmp positive coefficient negative).PolynomiallyTimed bound := by
  refine ⟨Polynomial.C (2+7*coefficient)*bound+Polynomial.C (1+2*coefficient+positive+negative),?_⟩
  intro n cs hb _
  have hs := hb source
  have ht := hb target
  simp only [counterAffineCopyProgramTemplate,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  nlinarith

/-- A finite affine accumulator advances the target without consuming the source. -/
noncomputable def counterAffineAccumulationProgramTemplate (a : AffineAtom R) (tmp : R) : CounterProgramTemplate R where
  Labels := AffineLabel a.offset a.coefficient
  finite := fun L f => by letI := f; infer_instance
  code := fun caller stop => affineCode caller a.offset a.coefficient a.source a.target tmp stop
  entry := fun stop => affineStart a.offset a.coefficient stop
  exit := fun l => .inr (.inr l)
  ready := fun cs => cs tmp=0
  steps := a.steps
  counters := a.apply
  bytes := fun _ => []

theorem counterAffineAccumulationProgramTemplate_embeds (a : AffineAtom R) (tmp : R) :
    (counterAffineAccumulationProgramTemplate a tmp).Embeds := by
  intro L caller stop l
  change ((caller l).relabel Sum.inr).relabel Sum.inr = _
  cases caller l <;> rfl

theorem counterAffineAccumulationProgramTemplate_run (a : AffineAtom R) (tmp : R) (ha : a.Valid tmp) :
    (counterAffineAccumulationProgramTemplate a tmp).Runs := by
  intro L caller stop cs ys hs
  exact a.run caller tmp stop ha cs hs ys

theorem counterAffineAccumulationProgramTemplate_polynomial (a : AffineAtom R) (tmp : R) (bound : Polynomial Nat) :
    (counterAffineAccumulationProgramTemplate a tmp).PolynomiallyTimed bound := by
  refine ⟨Polynomial.C (7*a.coefficient)*bound+Polynomial.C (2*a.coefficient+a.offset),?_⟩
  intro n cs hb _
  have hs := hb a.source
  simp only [counterAffineAccumulationProgramTemplate,AffineAtom.steps,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  nlinarith

end ShiReversibleGenerator
