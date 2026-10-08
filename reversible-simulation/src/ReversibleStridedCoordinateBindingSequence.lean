import ReversibleCoordinateBindingSequence
import ReversibleStridedTickCoordinateBindingClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R L : Type} [DecidableEq R]

noncomputable def StridedCoordinateBindingSequenceLabels (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat) :
    List (CoordinateBindingTask tm R) → Type → Type
  | [], L => L
  | task :: tasks, L => StridedTickCoordinateBindingLabels tm (env.withTarget task.2) inputStride task.1
      (StridedCoordinateBindingSequenceLabels tm env inputStride tasks L)

noncomputable def stridedCoordinateBindingSequenceEntry (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (stop : L) : StridedCoordinateBindingSequenceLabels tm env inputStride tasks L :=
  match tasks with
  | [] => stop
  | task :: tasks => stridedTickCoordinateBindingEntry tm (env.withTarget task.2) inputStride task.1
      (StridedCoordinateBindingSequenceLabels tm env inputStride tasks L)

noncomputable def stridedCoordinateBindingSequenceExit (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (l : L) : StridedCoordinateBindingSequenceLabels tm env inputStride tasks L :=
  match tasks with
  | [] => l
  | task :: tasks => stridedTickCoordinateBindingExit tm (env.withTarget task.2) inputStride task.1
      (stridedCoordinateBindingSequenceExit tm env inputStride tasks l)

noncomputable def stridedCoordinateBindingSequenceCode (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (caller : L → CounterInstr R L) (stop : L) :
    StridedCoordinateBindingSequenceLabels tm env inputStride tasks L → CounterInstr R (StridedCoordinateBindingSequenceLabels tm env inputStride tasks L) :=
  match tasks with
  | [] => caller
  | task :: tasks => stridedTickCoordinateBindingCode tm (env.withTarget task.2) inputStride task.1
      (stridedCoordinateBindingSequenceCode tm env inputStride tasks caller stop) (stridedCoordinateBindingSequenceEntry tm env inputStride tasks stop)

noncomputable def stridedCoordinateBindingSequenceCounters (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat) :
    List (CoordinateBindingTask tm R) → (R → Nat) → (R → Nat)
  | [], cs => cs
  | task :: tasks, cs => stridedCoordinateBindingSequenceCounters tm env inputStride tasks
      (Function.update cs task.2 (stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs))

noncomputable def stridedCoordinateBindingSequenceSteps (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat) :
    List (CoordinateBindingTask tm R) → (R → Nat) → Nat
  | [], _ => 0
  | task :: tasks, cs => stridedTickCoordinateBindingSteps tm (env.withTarget task.2) inputStride task.1 cs +
      stridedCoordinateBindingSequenceSteps tm env inputStride tasks
        (Function.update cs task.2 (stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs))

noncomputable instance stridedCoordinateBindingSequenceFintype (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) [Fintype L] : Fintype (StridedCoordinateBindingSequenceLabels tm env inputStride tasks L) := by
  induction tasks with
  | nil => exact inferInstanceAs (Fintype L)
  | cons task tasks ih =>
    letI := ih
    exact inferInstanceAs (Fintype (StridedTickCoordinateBindingLabels tm (env.withTarget task.2) inputStride task.1
      (StridedCoordinateBindingSequenceLabels tm env inputStride tasks L)))

theorem stridedCoordinateBindingSequenceCode_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (caller : L → CounterInstr R L) (stop : L)
    (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (cs : R → Nat) (hq : cs env.query = 0) (hx : cs env.tmp = 0) (ys : List Bool) :
    CounterRun (stridedCoordinateBindingSequenceCode tm env inputStride tasks caller stop)
      ⟨some (stridedCoordinateBindingSequenceEntry tm env inputStride tasks stop), cs, ys⟩ (stridedCoordinateBindingSequenceSteps tm env inputStride tasks cs)
      ⟨some (stridedCoordinateBindingSequenceExit tm env inputStride tasks stop), stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs, ys⟩ := by
  induction tasks generalizing cs with
  | nil => exact CounterRun.refl _
  | cons task tasks ih =>
    let inner := stridedCoordinateBindingSequenceCode tm env inputStride tasks caller stop
    let code := stridedCoordinateBindingSequenceCode tm env inputStride (task :: tasks) caller stop
    let after := Function.update cs task.2 (stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs)
    have hvalid := hv task (by simp)
    have hnq : env.query ≠ task.2 := hvalid.query_target
    have hnt : env.tmp ≠ task.2 := Ne.symm hvalid.target_tmp
    have h₁ := stridedTickCoordinateBindingCode_run tm (env.withTarget task.2) inputStride task.1 inner
      (stridedCoordinateBindingSequenceEntry tm env inputStride tasks stop) hvalid cs hq hx ys
    have h₂ := ih (fun t ht => hv t (by simp [ht])) after
      (by simp [after, hnq, hq]) (by simp [after, hnt, hx])
    have h₃ := CounterRun.relabel inner code (stridedTickCoordinateBindingExit tm (env.withTarget task.2) inputStride task.1)
      (fun _ => stridedTickCoordinateBindingCode_embed _ _ _ _ _ _ _) h₂
    have h := CounterRun.trans code h₁ h₃
    simpa only [code, inner, after, stridedCoordinateBindingSequenceEntry, stridedCoordinateBindingSequenceExit,
      stridedCoordinateBindingSequenceSteps, stridedCoordinateBindingSequenceCounters, CounterCfg.relabel, Option.map_some] using h

end ShiReversibleGenerator
