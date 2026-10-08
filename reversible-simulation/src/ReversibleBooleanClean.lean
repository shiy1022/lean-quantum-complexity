import ReversibleBoolean
import ReversibleCleanup

set_option autoImplicit false

namespace ShiReversible

theorem cleanAssignments_correct {n m : Nat} (c : List (Assignment n))
    (hn : (c.map Assignment.target).Nodup) (read : Fin m → Fin n)
    (s : Bits n) (hz : ∀ a ∈ c, s a.target = false) (y : Bits m) :
    execute (cleanCircuit (compileAssignments c) read) (s, y) =
      (s, fun i => xor (y i) (evalAssignments c s (read i))) := by
  rw [cleanCircuit_correct, compileAssignments_correct c hn s hz]

theorem cleanAssignments_size {n m : Nat} (c : List (Assignment n))
    (read : Fin m → Fin n) :
    (cleanCircuit (compileAssignments c) read).length ≤ 4 * c.length + m := by
  rw [cleanCircuit_length]
  have h := compileAssignments_length c
  omega

end ShiReversible
