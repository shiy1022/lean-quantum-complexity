import ReversibleStridedCoordinateBindingSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- Binding one slot cannot change the address any subsequent fixed task must compute. -/
theorem stridedCoordinateBindingAddress_after (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (task other : CoordinateBindingTask tm R) (hv : (env.withTarget task.2).Valid) (cs : R → Nat) :
    stridedTickCoordinateAddress tm (env.withTarget other.2) inputStride other.1
      (Function.update cs task.2 (stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs)) =
      stridedTickCoordinateAddress tm (env.withTarget other.2) inputStride other.1 cs := by
  have hi : env.input ≠ task.2 := hv.input_target
  have hc : env.capacity ≠ task.2 := hv.capacity_target
  have hp : env.position ≠ task.2 := hv.position_target
  simp [stridedTickCoordinateAddress, CoordinateBindingRegisters.withTarget, hi, hc, hp]

theorem stridedCoordinateBindingSequence_source_frames (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (cs : R → Nat) : ∀ q ∈ [env.input, env.capacity, env.position, env.query, env.tmp],
      stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs q = cs q := by
  induction tasks generalizing cs with
  | nil => intro q hq; rfl
  | cons task tasks ih =>
    intro q hq
    have hvalid := hv task (by simp)
    have h := ih (fun t ht => hv t (by simp [ht]))
      (Function.update cs task.2 (stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs)) q hq
    have hf := stridedTickCoordinateBinding_source_frame tm (env.withTarget task.2) inputStride task.1 hvalid cs q
      (by simpa [CoordinateBindingRegisters.withTarget] using hq)
    exact h.trans hf

theorem stridedCoordinateBindingSequence_preserves_other (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (q : R) (hne : ∀ task ∈ tasks, q ≠ task.2)
    (cs : R → Nat) : stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs q = cs q := by
  induction tasks generalizing cs with
  | nil => rfl
  | cons task tasks ih =>
    have h := ih (fun t ht => hne t (by simp [ht]))
      (Function.update cs task.2 (stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs))
    simpa only [stridedCoordinateBindingSequenceCounters, Function.update_of_ne (hne task (by simp))] using h

/-- Distinct finite slots contain the original tasks' exact addresses after the whole actual sequence. -/
theorem stridedCoordinateBindingSequence_slot_values (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (hd : tasks.Pairwise (fun a b => a.2 ≠ b.2)) (cs : R → Nat) :
    ∀ task ∈ tasks, stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs task.2 =
      stridedTickCoordinateAddress tm (env.withTarget task.2) inputStride task.1 cs := by
  induction tasks generalizing cs with
  | nil => simp
  | cons head tasks ih =>
    intro task ht
    have hvalid := hv head (by simp)
    have hp := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp ht with he | ht
    · subst task
      have h := stridedCoordinateBindingSequence_preserves_other tm env inputStride tasks head.2 hp.1
        (Function.update cs head.2 (stridedTickCoordinateAddress tm (env.withTarget head.2) inputStride head.1 cs))
      simpa only [stridedCoordinateBindingSequenceCounters, Function.update_self] using h
    · have h := ih (fun t hh => hv t (by simp [hh])) hp.2
        (Function.update cs head.2 (stridedTickCoordinateAddress tm (env.withTarget head.2) inputStride head.1 cs)) task ht
      exact h.trans (stridedCoordinateBindingAddress_after tm env inputStride head task hvalid cs)

end ShiReversibleGenerator
