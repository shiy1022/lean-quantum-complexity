import ReversibleProgramTemplateSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

def incrementProgramTemplate (r : R) : CounterProgramTemplate R where
  Labels := fun L => Unit ⊕ L
  finite := fun L f => by letI := f; infer_instance
  code := fun caller stop => Sum.elim (fun _ => .inc r (.inr stop)) (fun l => (caller l).relabel Sum.inr)
  entry := fun _ => .inl ()
  exit := Sum.inr
  ready := fun _ => True
  steps := fun _ => 1
  counters := fun cs => Function.update cs r (cs r + 1)
  bytes := fun _ => []

theorem incrementProgramTemplate_embeds (r : R) : (incrementProgramTemplate r).Embeds := by
  intro L caller stop l
  rfl

theorem incrementProgramTemplate_run (r : R) : (incrementProgramTemplate r).Runs := by
  intro L caller stop cs ys hready
  have h := CounterRun.one ((incrementProgramTemplate r).code caller stop)
    ⟨some (.inl ()), cs, ys⟩ (.inl ()) rfl
  simpa [incrementProgramTemplate, CounterInstr.eval] using h

theorem incrementProgramTemplate_polynomial (r : R) (bound : Polynomial Nat) :
    (incrementProgramTemplate r).PolynomiallyTimed bound := by
  exact ⟨1, by intro n cs hb hr; simp [incrementProgramTemplate]⟩

end ShiReversibleGenerator
