import ReversibleIncrementProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

def identityProgramTemplate : CounterProgramTemplate R where
  Labels := id
  finite := fun _ f => f
  code := fun caller _ => caller
  entry := id
  exit := id
  ready := fun _ => True
  steps := fun _ => 0
  counters := id
  bytes := fun _ => []

theorem identityProgramTemplate_embeds : (identityProgramTemplate (R := R)).Embeds := by
  intro L caller stop l
  change caller l = (caller l).relabel id
  cases caller l <;> rfl

theorem identityProgramTemplate_run : (identityProgramTemplate (R := R)).Runs := by
  intro L caller stop cs ys hr
  exact CounterRun.refl _

noncomputable def listProgramTemplate : List (CounterProgramTemplate R) → CounterProgramTemplate R
  | [] => identityProgramTemplate
  | p :: ps => sequenceProgramTemplate p (listProgramTemplate ps)

theorem listProgramTemplate_embeds (ps : List (CounterProgramTemplate R))
    (he : ∀ p ∈ ps, p.Embeds) : (listProgramTemplate ps).Embeds := by
  induction ps with
  | nil => exact identityProgramTemplate_embeds
  | cons p ps ih =>
    exact sequenceProgramTemplate_embeds _ _ (he p (by simp)) (ih (fun q hq => he q (by simp [hq])))

theorem listProgramTemplate_run (ps : List (CounterProgramTemplate R))
    (he : ∀ p ∈ ps, p.Embeds) (hr : ∀ p ∈ ps, p.Runs) : (listProgramTemplate ps).Runs := by
  induction ps with
  | nil => exact identityProgramTemplate_run
  | cons p ps ih =>
    exact sequenceProgramTemplate_run _ _ (he p (by simp)) (hr p (by simp))
      (ih (fun q hq => he q (by simp [hq])) (fun q hq => hr q (by simp [hq])))

end ShiReversibleGenerator
