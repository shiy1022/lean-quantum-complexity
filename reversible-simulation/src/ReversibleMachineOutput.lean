import ReversibleMachineExecution
import ReversibleOutput

set_option autoImplicit false

namespace ShiReversibleTM

theorem polyTime_output_length {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) (xs : List Bool) :
    (f xs).length ≤ xs.length + (M.time.eval xs.length) * machinePushBound M.tm := by
  have h := initial_trace_stack_length M.tm (M.time.eval xs.length)
    (xs.map M.inputAlphabet.invFun) M.tm.k₁
  rw [polyTime_padded_run M xs] at h
  simpa [Turing.haltList] using h

noncomputable def outputCapacity {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) : Polynomial Nat :=
  Polynomial.X + Polynomial.C (machinePushBound M.tm) * M.time

theorem polyTime_output_fits {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) (xs : List Bool) :
    (f xs).length ≤ (outputCapacity M).eval xs.length := by
  simpa [outputCapacity, Nat.mul_comm] using polyTime_output_length M xs

theorem polyTime_outputCode_width {f : List Bool → List Bool}
    (M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) f) (xs : List Bool) :
    (ShiReversible.outputCode ((outputCapacity M).eval xs.length) (f xs)).length =
      2 * (outputCapacity M).eval xs.length + 1 :=
  ShiReversible.outputCode_width _ _ (polyTime_output_fits M xs)

end ShiReversibleTM
