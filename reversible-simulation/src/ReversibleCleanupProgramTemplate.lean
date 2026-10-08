import ReversibleCounterCopyProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- A reusable finite cleanup program returns to its caller with the selected counters zero. -/
noncomputable def cleanupProgramTemplate (clear : List R) : CounterProgramTemplate R where
  Labels := CleanupLabels clear
  finite := fun L f => by letI := f; infer_instance
  code := cleanupCode clear
  entry := cleanupEntry clear
  exit := cleanupExit clear
  ready := fun _ => True
  steps := cleanupSteps clear
  counters := cleanupCounters clear
  bytes := fun _ => []

theorem cleanupProgramTemplate_embeds (clear : List R) : (cleanupProgramTemplate clear).Embeds := by
  intro L caller stop l
  exact cleanupCode_embed clear caller stop l

theorem cleanupProgramTemplate_run (clear : List R) : (cleanupProgramTemplate clear).Runs := by
  intro L caller stop cs ys _
  exact cleanupCode_run clear caller stop cs ys

theorem cleanupCounters_uniform_bound (clear : List R) (cs : R → Nat) (bound : Nat)
    (h : ∀ q,cs q ≤ bound) : ∀ q,cleanupCounters clear cs q ≤ bound := by
  intro q
  rw [cleanupCounters_apply]
  split
  · exact Nat.zero_le _
  · exact h q

theorem cleanupSteps_uniform_bound (clear : List R) (cs : R → Nat) (bound : Nat)
    (h : ∀ q,cs q ≤ bound) : cleanupSteps clear cs ≤ clear.length*(2*bound+1) := by
  induction clear generalizing cs with
  | nil => simp [cleanupSteps]
  | cons q clear ih =>
    have hnext : ∀ r, Function.update cs q 0 r ≤ bound := by
      intro r
      by_cases he : r=q
      · subst r; simp
      · simpa [he] using h r
    have hh := ih (Function.update cs q 0) hnext
    have hq := h q
    simp only [cleanupSteps,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem cleanupProgramTemplate_polynomial (clear : List R) (bound : Polynomial Nat) :
    (cleanupProgramTemplate clear).PolynomiallyTimed bound := by
  refine ⟨Polynomial.C clear.length*(Polynomial.C 2*bound+Polynomial.C 1),?_⟩
  intro n cs h _
  simpa only [cleanupProgramTemplate,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C]
    using cleanupSteps_uniform_bound clear cs (bound.eval n) h

end ShiReversibleGenerator
