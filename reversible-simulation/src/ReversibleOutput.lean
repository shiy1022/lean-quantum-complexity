import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ShiReversible

/-- A finite fixed-width output with an explicit length, before bit serialization. -/
structure PaddedOutput (capacity : Nat) where
  length : Nat
  length_le : length ≤ capacity
  data : List Bool
  data_length : data.length = capacity

def padOutput (capacity : Nat) (xs : List Bool) (h : xs.length ≤ capacity) :
    PaddedOutput capacity where
  length := xs.length
  length_le := h
  data := xs ++ List.replicate (capacity - xs.length) false
  data_length := by simp; omega

def decodeOutput {capacity : Nat} (output : PaddedOutput capacity) : List Bool :=
  output.data.take output.length

@[simp] theorem decode_padOutput (capacity : Nat) (xs : List Bool)
    (h : xs.length ≤ capacity) : decodeOutput (padOutput capacity xs h) = xs := by
  simp [decodeOutput, padOutput]

theorem padOutput_injective (capacity : Nat) (xs ys : List Bool)
    (hx : xs.length ≤ capacity) (hy : ys.length ≤ capacity)
    (h : padOutput capacity xs hx = padOutput capacity ys hy) : xs = ys := by
  simpa using congrArg decodeOutput h

/-- Unary length, false delimiter, payload, and zero padding; fixed width `2*capacity+1`. -/
def outputCode (capacity : Nat) (xs : List Bool) : List Bool :=
  List.replicate xs.length true ++ [false] ++ xs ++
    List.replicate (2 * (capacity - xs.length)) false

def outputDecode (code : List Bool) : List Bool :=
  let length := (code.takeWhile id).length
  (code.drop (length + 1)).take length

theorem truePrefix (length : Nat) (tail : List Bool) :
    (List.replicate length true ++ false :: tail).takeWhile id =
      List.replicate length true := by
  induction length with
  | zero => simp
  | succ length ih => simpa [List.replicate_succ] using congrArg (List.cons true) ih

theorem outputCode_width (capacity : Nat) (xs : List Bool) (h : xs.length ≤ capacity) :
    (outputCode capacity xs).length = 2 * capacity + 1 := by
  simp [outputCode]
  omega

@[simp] theorem outputDecode_code (capacity : Nat) (xs : List Bool) :
    outputDecode (outputCode capacity xs) = xs := by
  have hp := truePrefix xs.length (xs ++ List.replicate (2 * (capacity-xs.length)) false)
  unfold outputDecode outputCode
  simp only [List.append_assoc, List.singleton_append, hp, List.length_replicate]
  simp [List.drop_append]

theorem outputCode_injective (capacity : Nat) : Function.Injective (outputCode capacity) := by
  intro xs ys h
  simpa using congrArg outputDecode h

end ShiReversible
