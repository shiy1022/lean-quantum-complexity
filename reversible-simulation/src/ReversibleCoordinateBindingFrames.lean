import ReversibleCoordinateBindingSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- Binding one slot cannot change the address any subsequent fixed task must compute. -/
theorem coordinateBindingAddress_after (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (task other : CoordinateBindingTask tm R) (hv : (env.withTarget task.2).Valid) (cs : R → Nat) :
    tickCoordinateAddress tm (env.withTarget other.2) other.1
      (Function.update cs task.2 (tickCoordinateAddress tm (env.withTarget task.2) task.1 cs)) =
      tickCoordinateAddress tm (env.withTarget other.2) other.1 cs := by
  have hi : env.input ≠ task.2 := hv.input_target
  have hc : env.capacity ≠ task.2 := hv.capacity_target
  have hp : env.position ≠ task.2 := hv.position_target
  simp [tickCoordinateAddress, CoordinateBindingRegisters.withTarget, hi, hc, hp]

theorem coordinateBindingSequence_source_frames (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (cs : R → Nat) : ∀ q ∈ [env.input, env.capacity, env.position, env.query, env.tmp],
      coordinateBindingSequenceCounters tm env tasks cs q = cs q := by
  induction tasks generalizing cs with
  | nil => intro q hq; rfl
  | cons task tasks ih =>
    intro q hq
    have hvalid := hv task (by simp)
    have h := ih (fun t ht => hv t (by simp [ht]))
      (Function.update cs task.2 (tickCoordinateAddress tm (env.withTarget task.2) task.1 cs)) q hq
    have hf := tickCoordinateBinding_source_frame tm (env.withTarget task.2) task.1 hvalid cs q
      (by simpa [CoordinateBindingRegisters.withTarget] using hq)
    exact h.trans hf

theorem coordinateBindingSequence_preserves_other (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (q : R) (hne : ∀ task ∈ tasks, q ≠ task.2)
    (cs : R → Nat) : coordinateBindingSequenceCounters tm env tasks cs q = cs q := by
  induction tasks generalizing cs with
  | nil => rfl
  | cons task tasks ih =>
    have h := ih (fun t ht => hne t (by simp [ht]))
      (Function.update cs task.2 (tickCoordinateAddress tm (env.withTarget task.2) task.1 cs))
    simpa only [coordinateBindingSequenceCounters, Function.update_of_ne (hne task (by simp))] using h

/-- Distinct finite slots contain the original tasks' exact addresses after the whole actual sequence. -/
theorem coordinateBindingSequence_slot_values (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (hd : tasks.Pairwise (fun a b => a.2 ≠ b.2)) (cs : R → Nat) :
    ∀ task ∈ tasks, coordinateBindingSequenceCounters tm env tasks cs task.2 =
      tickCoordinateAddress tm (env.withTarget task.2) task.1 cs := by
  induction tasks generalizing cs with
  | nil => simp
  | cons head tasks ih =>
    intro task ht
    have hvalid := hv head (by simp)
    have hp := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp ht with he | ht
    · subst task
      have h := coordinateBindingSequence_preserves_other tm env tasks head.2 hp.1
        (Function.update cs head.2 (tickCoordinateAddress tm (env.withTarget head.2) head.1 cs))
      simpa only [coordinateBindingSequenceCounters, Function.update_self] using h
    · have h := ih (fun t hh => hv t (by simp [hh])) hp.2
        (Function.update cs head.2 (tickCoordinateAddress tm (env.withTarget head.2) head.1 cs)) task ht
      exact h.trans (coordinateBindingAddress_after tm env head task hvalid cs)

end ShiReversibleGenerator
