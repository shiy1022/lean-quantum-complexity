import ReversibleCore

set_option autoImplicit false

namespace ShiReversible

theorem execute_copies {n m : Nat} (read : Fin m → Fin n) (l : List (Fin m))
    (h : l.Nodup) (s : Bits n) (y : Bits m) :
    execute (l.map (fun i => Instruction.copy (read i) i)) (s, y) =
      (s, fun i => if i ∈ l then xor (y i) (s (read i)) else y i) := by
  induction l generalizing y with
  | nil => simp [execute]
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.mp h).1
    have hl : l.Nodup := (List.nodup_cons.mp h).2
    change execute (l.map (fun i => Instruction.copy (read i) i))
      (s, Function.update y a (xor (y a) (s (read a)))) = _
    rw [ih hl]
    apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i = a
      · subst i; simp [ha]
      · simp [hi, Function.update_of_ne hi]

theorem execute_copyOut {n m : Nat} (read : Fin m → Fin n) (s : Bits n) (y : Bits m) :
    execute (copyOut read) (s, y) = (s, fun i => xor (y i) (s (read i))) := by
  simpa [copyOut] using execute_copies read (List.finRange m) (List.nodup_finRange m) s y

/-- Exact cleanup for any actual gate list and any designated output wires. -/
theorem cleanCircuit_correct {n m : Nat} (c : List (Gate n))
    (read : Fin m → Fin n) (s : Bits n) (y : Bits m) :
    execute (cleanCircuit c read) (s, y) =
      (s, fun i => xor (y i) (run c s (read i))) := by
  simp only [cleanCircuit, execute_append, execute_work, execute_copyOut,
    run_reverse_run]

theorem cleanCircuit_zero_output {n m : Nat} (c : List (Gate n))
    (read : Fin m → Fin n) (s : Bits n) :
    execute (cleanCircuit c read) (s, fun _ => false) =
      (s, fun i => run c s (read i)) := by
  simpa using cleanCircuit_correct c read s (fun _ => false)

end ShiReversible
