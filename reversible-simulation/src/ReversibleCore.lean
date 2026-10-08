import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ShiReversible

abbrev Bits (n : Nat) := Fin n → Bool

/-- Each instruction is an actual bounded-arity reversible Boolean gate. -/
inductive Gate (n : Nat) where
  | x (t : Fin n)
  | cx (c t : Fin n) (h : c ≠ t)
  | ccx (a b t : Fin n) (ha : a ≠ t) (hb : b ≠ t)

def Gate.eval {n : Nat} : Gate n → Bits n → Bits n
  | .x t, s => Function.update s t (!s t)
  | .cx c t _, s => Function.update s t (xor (s t) (s c))
  | .ccx a b t _ _, s => Function.update s t (xor (s t) (s a && s b))

theorem Gate.involutive {n : Nat} (g : Gate n) : Function.Involutive g.eval := by
  intro s
  cases g with
  | x t =>
    funext i
    by_cases h : i = t
    · subst i; simp [Gate.eval]
    · simp [Gate.eval, Function.update_of_ne h]
  | cx c t hct =>
    funext i
    by_cases h : i = t
    · subst i
      simp [Gate.eval, Function.update_of_ne hct]
    · simp [Gate.eval, Function.update_of_ne h]
  | ccx a b t hat hbt =>
    funext i
    by_cases h : i = t
    · subst i
      simp [Gate.eval, Function.update_of_ne hat, Function.update_of_ne hbt]
    · simp [Gate.eval, Function.update_of_ne h]

def run {n : Nat} (c : List (Gate n)) (s : Bits n) : Bits n :=
  c.foldl (fun s g => g.eval s) s

@[simp] theorem run_nil {n : Nat} (s : Bits n) : run [] s = s := rfl

@[simp] theorem run_cons {n : Nat} (g : Gate n) (c : List (Gate n)) (s : Bits n) :
    run (g :: c) s = run c (g.eval s) := rfl

theorem run_append {n : Nat} (c d : List (Gate n)) (s : Bits n) :
    run (c ++ d) s = run d (run c s) := by
  simp [run, List.foldl_append]

theorem run_reverse_run {n : Nat} (c : List (Gate n)) (s : Bits n) :
    run c.reverse (run c s) = s := by
  induction c generalizing s with
  | nil => rfl
  | cons g c ih =>
    rw [run_cons, List.reverse_cons, run_append, ih]
    exact g.involutive s

def circuitPerm {n : Nat} (c : List (Gate n)) : Equiv.Perm (Bits n) where
  toFun := run c
  invFun := run c.reverse
  left_inv := run_reverse_run c
  right_inv := by
    intro s
    simpa using run_reverse_run c.reverse s

/-- The external output register is separate from all computation wires. -/
abbrev Registers (n m : Nat) := Bits n × Bits m

inductive Instruction (n m : Nat) where
  | work (g : Gate n)
  | copy (source : Fin n) (target : Fin m)

def Instruction.eval {n m : Nat} : Instruction n m → Registers n m → Registers n m
  | .work g, (s, y) => (g.eval s, y)
  | .copy r t, (s, y) => (s, Function.update y t (xor (y t) (s r)))

theorem Instruction.involutive {n m : Nat} (g : Instruction n m) :
    Function.Involutive g.eval := by
  rintro ⟨s, y⟩
  cases g with
  | work g => simp [Instruction.eval, g.involutive s]
  | copy r t =>
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : i = t
      · subst i; simp [Instruction.eval]
      · simp [Instruction.eval, Function.update_of_ne h]

def execute {n m : Nat} (c : List (Instruction n m)) (s : Registers n m) :=
  c.foldl (fun s g => g.eval s) s

theorem execute_append {n m : Nat} (c d : List (Instruction n m)) (s : Registers n m) :
    execute (c ++ d) s = execute d (execute c s) := by
  simp [execute, List.foldl_append]

theorem execute_work {n m : Nat} (c : List (Gate n)) (s : Bits n) (y : Bits m) :
    execute (c.map Instruction.work) (s, y) = (run c s, y) := by
  induction c generalizing s with
  | nil => rfl
  | cons g c ih => simpa [execute, run, Instruction.eval] using ih (g.eval s)

/-- Copy each selected work wire into its corresponding output wire. -/
def copyOut {n m : Nat} (read : Fin m → Fin n) : List (Instruction n m) :=
  (List.finRange m).map (fun i => .copy (read i) i)

/-- Gate-level Bennett construction. The inverse is the reversed gate list. -/
def cleanCircuit {n m : Nat} (c : List (Gate n)) (read : Fin m → Fin n) :=
  c.map Instruction.work ++ copyOut read ++ c.reverse.map Instruction.work

theorem cleanCircuit_length {n m : Nat} (c : List (Gate n)) (read : Fin m → Fin n) :
    (cleanCircuit c read).length = 2 * c.length + m := by
  simp [cleanCircuit, copyOut]
  omega

end ShiReversible
