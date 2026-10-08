import ReversibleCellBindingContinuations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R L : Type} [DecidableEq R]

def CoordinateBindingRegisters.withTarget (env : CoordinateBindingRegisters R) (target : R) :
    CoordinateBindingRegisters R := { env with target := target }

abbrev CoordinateBindingTask (tm : Turing.FinTM2) (R : Type) := TickSymbolicCoordinate tm × R

noncomputable def CoordinateBindingSequenceLabels (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) :
    List (CoordinateBindingTask tm R) → Type → Type
  | [], L => L
  | task :: tasks, L => TickCoordinateBindingLabels tm (env.withTarget task.2) task.1
      (CoordinateBindingSequenceLabels tm env tasks L)

noncomputable def coordinateBindingSequenceEntry (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (stop : L) : CoordinateBindingSequenceLabels tm env tasks L :=
  match tasks with
  | [] => stop
  | task :: tasks => tickCoordinateBindingEntry tm (env.withTarget task.2) task.1
      (CoordinateBindingSequenceLabels tm env tasks L)

noncomputable def coordinateBindingSequenceExit (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (l : L) : CoordinateBindingSequenceLabels tm env tasks L :=
  match tasks with
  | [] => l
  | task :: tasks => tickCoordinateBindingExit tm (env.withTarget task.2) task.1
      (coordinateBindingSequenceExit tm env tasks l)

noncomputable def coordinateBindingSequenceCode (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (caller : L → CounterInstr R L) (stop : L) :
    CoordinateBindingSequenceLabels tm env tasks L → CounterInstr R (CoordinateBindingSequenceLabels tm env tasks L) :=
  match tasks with
  | [] => caller
  | task :: tasks => tickCoordinateBindingCode tm (env.withTarget task.2) task.1
      (coordinateBindingSequenceCode tm env tasks caller stop) (coordinateBindingSequenceEntry tm env tasks stop)

noncomputable def coordinateBindingSequenceCounters (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) :
    List (CoordinateBindingTask tm R) → (R → Nat) → (R → Nat)
  | [], cs => cs
  | task :: tasks, cs => coordinateBindingSequenceCounters tm env tasks
      (Function.update cs task.2 (tickCoordinateAddress tm (env.withTarget task.2) task.1 cs))

noncomputable def coordinateBindingSequenceSteps (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) :
    List (CoordinateBindingTask tm R) → (R → Nat) → Nat
  | [], _ => 0
  | task :: tasks, cs => tickCoordinateBindingSteps tm (env.withTarget task.2) task.1 cs +
      coordinateBindingSequenceSteps tm env tasks
        (Function.update cs task.2 (tickCoordinateAddress tm (env.withTarget task.2) task.1 cs))

noncomputable instance coordinateBindingSequenceFintype (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) [Fintype L] : Fintype (CoordinateBindingSequenceLabels tm env tasks L) := by
  induction tasks with
  | nil => exact inferInstanceAs (Fintype L)
  | cons task tasks ih =>
    letI := ih
    exact inferInstanceAs (Fintype (TickCoordinateBindingLabels tm (env.withTarget task.2) task.1
      (CoordinateBindingSequenceLabels tm env tasks L)))

theorem coordinateBindingSequenceCode_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (caller : L → CounterInstr R L) (stop : L)
    (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (cs : R → Nat) (hq : cs env.query = 0) (hx : cs env.tmp = 0) (ys : List Bool) :
    CounterRun (coordinateBindingSequenceCode tm env tasks caller stop)
      ⟨some (coordinateBindingSequenceEntry tm env tasks stop), cs, ys⟩ (coordinateBindingSequenceSteps tm env tasks cs)
      ⟨some (coordinateBindingSequenceExit tm env tasks stop), coordinateBindingSequenceCounters tm env tasks cs, ys⟩ := by
  induction tasks generalizing cs with
  | nil => exact CounterRun.refl _
  | cons task tasks ih =>
    let inner := coordinateBindingSequenceCode tm env tasks caller stop
    let code := coordinateBindingSequenceCode tm env (task :: tasks) caller stop
    let after := Function.update cs task.2 (tickCoordinateAddress tm (env.withTarget task.2) task.1 cs)
    have hvalid := hv task (by simp)
    have hnq : env.query ≠ task.2 := hvalid.query_target
    have hnt : env.tmp ≠ task.2 := Ne.symm hvalid.target_tmp
    have h₁ := tickCoordinateBindingCode_run tm (env.withTarget task.2) task.1 inner
      (coordinateBindingSequenceEntry tm env tasks stop) hvalid cs hq hx ys
    have h₂ := ih (fun t ht => hv t (by simp [ht])) after
      (by simp [after, hnq, hq]) (by simp [after, hnt, hx])
    have h₃ := CounterRun.relabel inner code (tickCoordinateBindingExit tm (env.withTarget task.2) task.1)
      (fun _ => tickCoordinateBindingCode_embed _ _ _ _ _ _) h₂
    have h := CounterRun.trans code h₁ h₃
    simpa only [code, inner, after, coordinateBindingSequenceEntry, coordinateBindingSequenceExit,
      coordinateBindingSequenceSteps, coordinateBindingSequenceCounters, CounterCfg.relabel, Option.map_some] using h

end ShiReversibleGenerator
