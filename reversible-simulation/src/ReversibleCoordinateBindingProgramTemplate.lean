import ReversibleStridedTickCoordinateBindingClock
import ReversibleProgramTemplateSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- One concrete finite coordinate binder as a composable instruction graph. -/
noncomputable def coordinateBindingProgramTemplate (tm : Turing.FinTM2)
    (r : CoordinateBindingRegisters R) (stride : Nat) (coordinate : TickSymbolicCoordinate tm) :
    CounterProgramTemplate R where
  Labels := StridedTickCoordinateBindingLabels tm r stride coordinate
  finite := fun L f => by letI := f; infer_instance
  code := stridedTickCoordinateBindingCode tm r stride coordinate
  entry := fun _ => stridedTickCoordinateBindingEntry tm r stride coordinate _
  exit := stridedTickCoordinateBindingExit tm r stride coordinate
  ready := fun cs => cs r.query=0 ∧ cs r.tmp=0
  steps := stridedTickCoordinateBindingSteps tm r stride coordinate
  counters := fun cs => Function.update cs r.target (stridedTickCoordinateAddress tm r stride coordinate cs)
  bytes := fun _ => []

theorem coordinateBindingProgramTemplate_embeds (tm : Turing.FinTM2)
    (r : CoordinateBindingRegisters R) (stride : Nat) (coordinate : TickSymbolicCoordinate tm) :
    (coordinateBindingProgramTemplate tm r stride coordinate).Embeds := by
  intro L caller stop l
  exact stridedTickCoordinateBindingCode_embed tm r stride coordinate caller stop l

theorem coordinateBindingProgramTemplate_run (tm : Turing.FinTM2)
    (r : CoordinateBindingRegisters R) (stride : Nat) (coordinate : TickSymbolicCoordinate tm) (hv : r.Valid) :
    (coordinateBindingProgramTemplate tm r stride coordinate).Runs := by
  intro L caller stop cs ys hr
  exact stridedTickCoordinateBindingCode_run tm r stride coordinate caller stop hv cs hr.1 hr.2 ys

theorem coordinateBindingProgramTemplate_polynomial (tm : Turing.FinTM2)
    (r : CoordinateBindingRegisters R) (stride : Nat) (coordinate : TickSymbolicCoordinate tm)
    (hv : r.Valid) (bound : Polynomial Nat) :
    (coordinateBindingProgramTemplate tm r stride coordinate).PolynomiallyTimed bound := by
  obtain ⟨clock,hclock⟩ := stridedTickCoordinateBindingSteps_polynomial tm r stride coordinate hv bound
  exact ⟨clock,fun n cs hb _ => hclock n cs hb⟩

end ShiReversibleGenerator
