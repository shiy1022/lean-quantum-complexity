import ReversibleProgramTemplateReentry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

noncomputable def templateDescendingBody (p : CounterProgramTemplate R) (remaining : R)
    (k : Nat) (s : CounterCfg R L) : CounterCfg R L :=
  let cs := Function.update s.counters remaining k
  ⟨none,p.counters cs,p.bytes cs ++ s.output⟩

noncomputable def templateDescendingCost (p : CounterProgramTemplate R) (remaining : R)
    (k : Nat) (s : CounterCfg R L) : Nat := p.steps (Function.update s.counters remaining k)

noncomputable def descendingTemplateCounters (p : CounterProgramTemplate R) (remaining : R) :
    Nat → (R → Nat) → R → Nat
  | 0,cs => cs
  | k+1,cs => descendingTemplateCounters p remaining k (p.counters (Function.update cs remaining k))

noncomputable def descendingTemplateBytes (p : CounterProgramTemplate R) (remaining : R) :
    Nat → (R → Nat) → List Bool
  | 0,_ => []
  | k+1,cs =>
    let next := Function.update cs remaining k
    descendingTemplateBytes p remaining k (p.counters next) ++ p.bytes next

noncomputable def descendingTemplateSteps (p : CounterProgramTemplate R) (remaining : R) :
    Nat → (R → Nat) → Nat
  | 0,_ => 1
  | k+1,cs =>
    let next := Function.update cs remaining k
    2+p.steps next+descendingTemplateSteps p remaining k (p.counters next)

noncomputable def descendingTemplateReady (p : CounterProgramTemplate R) (remaining : R) :
    Nat → (R → Nat) → Prop
  | 0,_ => True
  | k+1,cs =>
    let next := Function.update cs remaining k
    p.ready next ∧ p.counters next remaining = k ∧ descendingTemplateReady p remaining k (p.counters next)

theorem descendingTemplateResult_counters (p : CounterProgramTemplate R) (remaining : R)
    (k : Nat) (s : CounterCfg R L) :
    (descendingResult (templateDescendingBody p remaining) k s).counters =
      descendingTemplateCounters p remaining k s.counters := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

theorem descendingTemplateResult_output (p : CounterProgramTemplate R) (remaining : R)
    (k : Nat) (s : CounterCfg R L) :
    (descendingResult (templateDescendingBody p remaining) k s).output =
      descendingTemplateBytes p remaining k s.counters ++ s.output := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [descendingResult,ih]
    simp only [templateDescendingBody,descendingTemplateBytes,List.append_assoc]

theorem descendingTemplateSteps_eq (p : CounterProgramTemplate R) (remaining : R)
    (k : Nat) (s : CounterCfg R L) :
    descendingSteps (templateDescendingBody p remaining) (templateDescendingCost p remaining) k s =
      descendingTemplateSteps p remaining k s.counters := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [descendingSteps,ih]
    rfl

end ShiReversibleGenerator
