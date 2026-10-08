import ReversibleCleanup
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace ShiReversible

theorem execute_reverse_execute {n m : Nat} (c : List (Instruction n m))
    (s : Registers n m) : execute c.reverse (execute c s) = s := by
  induction c generalizing s with
  | nil => rfl
  | cons g c ih =>
    change execute (g :: c).reverse (execute c (g.eval s)) = s
    rw [List.reverse_cons, execute_append, ih]
    exact g.involutive s

def programPerm {n m : Nat} (c : List (Instruction n m)) : Equiv.Perm (Registers n m) where
  toFun := execute c
  invFun := execute c.reverse
  left_inv := execute_reverse_execute c
  right_inv := by
    intro s
    simpa using execute_reverse_execute c.reverse s

@[simp] theorem programPerm_apply {n m : Nat} (c : List (Instruction n m))
    (s : Registers n m) : programPerm c s = execute c s := rfl

abbrev QuantumState (n m : Nat) := Registers n m → ℂ

def basis {n m : Nat} (s : Registers n m) : QuantumState n m :=
  fun z => if z = s then 1 else 0

/-- Forward state evolution is pullback along the inverse basis permutation. -/
def quantumRun {n m : Nat} (c : List (Instruction n m)) (ψ : QuantumState n m) :
    QuantumState n m := fun z => ψ ((programPerm c).symm z)

theorem quantumRun_basis {n m : Nat} (c : List (Instruction n m)) (s : Registers n m) :
    quantumRun c (basis s) = basis (execute c s) := by
  funext z
  have h : (programPerm c).symm z = s ↔ z = execute c s := by
    constructor
    · intro h
      have hh := congrArg (programPerm c) h
      simpa only [Equiv.apply_symm_apply, programPerm_apply] using hh
    · intro h
      subst z
      exact (programPerm c).symm_apply_apply s
  simp only [quantumRun, basis, h]

theorem quantumRun_add {n m : Nat} (c : List (Instruction n m))
    (ψ φ : QuantumState n m) : quantumRun c (ψ + φ) = quantumRun c ψ + quantumRun c φ := rfl

theorem quantumRun_smul {n m : Nat} (c : List (Instruction n m))
    (a : ℂ) (ψ : QuantumState n m) : quantumRun c (a • ψ) = a • quantumRun c ψ := rfl

theorem quantumRun_inverse {n m : Nat} (c : List (Instruction n m)) (ψ : QuantumState n m) :
    quantumRun c.reverse (quantumRun c ψ) = ψ := by
  funext z
  change ψ (execute c.reverse (execute c.reverse.reverse z)) = ψ z
  simp only [List.reverse_reverse, execute_reverse_execute]

noncomputable def normSquared {n m : Nat} (ψ : QuantumState n m) : ℝ :=
  ∑ z, ‖ψ z‖ ^ 2

theorem quantumRun_normSquared {n m : Nat} (c : List (Instruction n m))
    (ψ : QuantumState n m) : normSquared (quantumRun c ψ) = normSquared ψ := by
  classical
  unfold normSquared quantumRun
  exact Fintype.sum_equiv (programPerm c).symm _ _ (fun _ => rfl)

/-- Exact basis-state Bennett cleanup, with arbitrary initial output contents. -/
theorem quantum_clean_correct {n m : Nat} (c : List (Gate n))
    (read : Fin m → Fin n) (s : Bits n) (y : Bits m) :
    quantumRun (cleanCircuit c read) (basis (s, y)) =
      basis (s, fun i => xor (y i) (run c s (read i))) := by
  rw [quantumRun_basis, cleanCircuit_correct]

end ShiReversible
