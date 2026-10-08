import ReversibleDescendingProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- Runtime copy for traversal setup: replace the target, preserve the source and clear scratch. -/
noncomputable def counterCopyProgramTemplate (source target tmp : R) : CounterProgramTemplate R where
  Labels := AddressBindingLabels 0 1 0
  finite := fun L f => by letI := f; infer_instance
  code := fun caller stop => addressBindingCode caller source target tmp 0 1 0 stop
  entry := fun _ => .inl 0
  exit := fun l => .inr (.inr (.inr (.inr l)))
  ready := fun cs => cs tmp = 0
  steps := fun cs => 2*cs target+1+(7*cs source+2)
  counters := fun cs => Function.update cs target (cs source)
  bytes := fun _ => []

theorem counterCopyProgramTemplate_embeds (source target tmp : R) :
    (counterCopyProgramTemplate source target tmp).Embeds := by
  intro L caller stop l
  exact addressBindingCode_embed caller source target tmp 0 1 0 stop l

theorem counterCopyProgramTemplate_run (source target tmp : R)
    (hst : source ≠ target) (hsx : source ≠ tmp) (htx : target ≠ tmp) :
    (counterCopyProgramTemplate source target tmp).Runs := by
  intro L caller stop cs ys hs
  simpa only [counterCopyProgramTemplate,Nat.one_mul,Nat.add_zero,Nat.sub_zero,List.nil_append]
    using addressBindingCode_run caller source target tmp 0 1 0 stop hst hsx htx cs hs ys

theorem counterCopyProgramTemplate_polynomial (source target tmp : R) (bound : Polynomial Nat) :
    (counterCopyProgramTemplate source target tmp).PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 9*bound+Polynomial.C 3,?_⟩
  intro n cs hb _
  have hs := hb source
  have ht := hb target
  simp only [counterCopyProgramTemplate,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
