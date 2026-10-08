import ReversibleTickForwardIterationCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

def decrementProgramTemplate (r : R) : CounterProgramTemplate R where
  Labels := fun L => Unit ⊕ L
  finite := fun L f => by letI := f; infer_instance
  code := fun caller stop => Sum.elim (fun _ => .dec r (.inr stop)) (fun l => (caller l).relabel Sum.inr)
  entry := fun _ => .inl ()
  exit := Sum.inr
  ready := fun _ => True
  steps := fun _ => 1
  counters := fun cs => Function.update cs r (cs r - 1)
  bytes := fun _ => []

theorem decrementProgramTemplate_embeds (r : R) : (decrementProgramTemplate r).Embeds := by
  intro L caller stop l
  rfl

theorem decrementProgramTemplate_run (r : R) : (decrementProgramTemplate r).Runs := by
  intro L caller stop cs ys hready
  have h := CounterRun.one ((decrementProgramTemplate r).code caller stop)
    ⟨some (.inl ()), cs, ys⟩ (.inl ()) rfl
  simpa [decrementProgramTemplate, CounterInstr.eval] using h

theorem decrementProgramTemplate_polynomial (r : R) (bound : Polynomial Nat) :
    (decrementProgramTemplate r).PolynomiallyTimed bound := by
  exact ⟨1, by intro n cs hb hr; simp [decrementProgramTemplate]⟩

end ShiReversibleGenerator
