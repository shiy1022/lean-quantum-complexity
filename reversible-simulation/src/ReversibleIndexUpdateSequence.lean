import ReversibleIndexUpdateProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

def IndexUpdateLabels : List IndexUpdate → Type → Type
  | [], L => L
  | op :: ops, L => ConstantLabel op.amount (IndexUpdateLabels ops L)

def indexUpdateEntry (ops : List IndexUpdate) (stop : L) : IndexUpdateLabels ops L :=
  match ops with
  | [] => stop
  | op :: ops => constantFrom op.amount (indexUpdateEntry ops stop) 0

def indexUpdateExit (ops : List IndexUpdate) (l : L) : IndexUpdateLabels ops L :=
  match ops with
  | [] => l
  | _ :: ops => .inr (indexUpdateExit ops l)

def indexUpdateCode (ops : List IndexUpdate) (caller : L → CounterInstr R L) (target : R) (stop : L) :
    IndexUpdateLabels ops L → CounterInstr R (IndexUpdateLabels ops L) :=
  match ops with
  | [] => caller
  | op :: ops => op.code (indexUpdateCode ops caller target stop) target (indexUpdateEntry ops stop)

def indexUpdateValue (ops : List IndexUpdate) (value : Nat) : Nat :=
  match ops with
  | [] => value
  | op :: ops => indexUpdateValue ops (op.apply value)

def indexUpdateSteps (ops : List IndexUpdate) : Nat := (ops.map IndexUpdate.amount).sum

theorem indexUpdateCode_embed (ops : List IndexUpdate) (caller : L → CounterInstr R L)
    (target : R) (stop l : L) :
    indexUpdateCode ops caller target stop (indexUpdateExit ops l) =
      (caller l).relabel (indexUpdateExit ops) := by
  induction ops with
  | nil =>
    change caller l = (caller l).relabel (fun x => x)
    cases caller l <;> rfl
  | cons op ops ih =>
    rw [indexUpdateCode, indexUpdateExit, IndexUpdate.code_embed, ih]
    cases caller l <;> rfl

theorem indexUpdateCode_run (ops : List IndexUpdate) (caller : L → CounterInstr R L)
    (target : R) (stop : L) (cs : R → Nat) (ys : List Bool) :
    CounterRun (indexUpdateCode ops caller target stop)
      ⟨some (indexUpdateEntry ops stop), cs, ys⟩ (indexUpdateSteps ops)
      ⟨some (indexUpdateExit ops stop), Function.update cs target (indexUpdateValue ops (cs target)), ys⟩ := by
  induction ops generalizing cs with
  | nil =>
    simpa [indexUpdateCode, indexUpdateEntry, indexUpdateExit, indexUpdateSteps, indexUpdateValue] using
      CounterRun.refl (⟨some stop, cs, ys⟩ : CounterCfg R L)
  | cons op ops ih =>
    let inner := indexUpdateCode ops caller target stop
    let outer := indexUpdateCode (op :: ops) caller target stop
    have h₁ := op.code_run inner target (indexUpdateEntry ops stop) cs ys
    have h₂ := ih (Function.update cs target (op.apply (cs target)))
    have h₃ := CounterRun.relabel inner outer Sum.inr (fun _ => IndexUpdate.code_embed _ _ _ _ _) h₂
    change CounterRun outer
      ⟨some (.inr (indexUpdateEntry ops stop)), Function.update cs target (op.apply (cs target)), ys⟩
      (indexUpdateSteps ops)
      ⟨some (.inr (indexUpdateExit ops stop)),
        Function.update (Function.update cs target (op.apply (cs target))) target
          (indexUpdateValue ops ((Function.update cs target (op.apply (cs target))) target)), ys⟩ at h₃
    have h := CounterRun.trans outer h₁ h₃
    simpa [outer, indexUpdateEntry, indexUpdateExit, indexUpdateSteps, indexUpdateValue] using h

theorem indexUpdateValue_append (ops tail : List IndexUpdate) (value : Nat) :
    indexUpdateValue (ops ++ tail) value = indexUpdateValue tail (indexUpdateValue ops value) := by
  induction ops generalizing value with
  | nil => rfl
  | cons op ops ih => exact ih (op.apply value)

noncomputable instance indexUpdateLabelsFintype (ops : List IndexUpdate) [Fintype L] :
    Fintype (IndexUpdateLabels ops L) := by
  induction ops with
  | nil => exact inferInstanceAs (Fintype L)
  | cons op ops ih =>
    letI := ih
    exact inferInstanceAs (Fintype (ConstantLabel op.amount (IndexUpdateLabels ops L)))

end ShiReversibleGenerator
