import ReversibleGateSubstitution
import ReversibleQuantum

set_option autoImplicit false
namespace ShiReversibleGateBridge
open ShiReversible

/-- The same registers, with the computation block followed by the output block. -/
def registerEquiv (n m : Nat) : Registers n m ≃ Bits (n + m) where
  toFun s := Fin.append s.1 s.2
  invFun x := (fun i => x (Fin.castAdd m i), fun i => x (Fin.natAdd n i))
  left_inv s := by apply Prod.ext <;> funext i <;> simp
  right_inv x := Fin.append_castAdd_natAdd

theorem left_ne_right {n m : Nat} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  omega

theorem append_update_left {n m : Nat} (s : Bits n) (y : Bits m) (t : Fin n) (b : Bool) :
    Fin.append (Function.update s t b) y = Function.update (Fin.append s y) (Fin.castAdd m t) b := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Function.update_apply, Fin.castAdd_inj]
  · simp [Function.update_apply, Ne.symm (left_ne_right t j)]

theorem append_update_right {n m : Nat} (s : Bits n) (y : Bits m) (t : Fin m) (b : Bool) :
    Fin.append s (Function.update y t b) = Function.update (Fin.append s y) (Fin.natAdd n t) b := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Function.update_apply, left_ne_right j t]
  · simp [Function.update_apply, Fin.ext_iff]

def workGate {n m : Nat} : Gate n → Gate (n + m)
  | .x t => .x (Fin.castAdd m t)
  | .cx a t hat => .cx (Fin.castAdd m a) (Fin.castAdd m t)
      (fun h => hat ((Fin.castAdd_injective n m) h))
  | .ccx a b t hat hbt => .ccx (Fin.castAdd m a) (Fin.castAdd m b) (Fin.castAdd m t)
      (fun h => hat ((Fin.castAdd_injective n m) h))
      (fun h => hbt ((Fin.castAdd_injective n m) h))

def flatInstruction {n m : Nat} : Instruction n m → Gate (n + m)
  | .work g => workGate g
  | .copy r t => .cx (Fin.castAdd m r) (Fin.natAdd n t) (left_ne_right r t)

theorem flatInstruction_correct {n m : Nat} (g : Instruction n m) (s : Registers n m) :
    (flatInstruction g).eval (registerEquiv n m s) = registerEquiv n m (g.eval s) := by
  rcases s with ⟨s, y⟩
  cases g with
  | work g =>
    cases g <;> simp only [flatInstruction, workGate, Gate.eval, registerEquiv, Instruction.eval,
      Equiv.coe_fn_mk, Fin.append_left] <;> exact (append_update_left _ _ _ _).symm
  | copy r t =>
    simp only [flatInstruction, Gate.eval, registerEquiv, Instruction.eval, Equiv.coe_fn_mk,
      Fin.append_left, Fin.append_right]
    exact (append_update_right _ _ _ _).symm

theorem flatProgram_correct {n m : Nat} (c : List (Instruction n m)) (s : Registers n m) :
    run (c.map flatInstruction) (registerEquiv n m s) = registerEquiv n m (execute c s) := by
  induction c generalizing s with
  | nil => rfl
  | cons g c ih =>
    simp only [List.map_cons, run_cons, flatInstruction_correct]
    exact ih (g.eval s)

/-- Existing quantum gate semantics exactly transport the reversible register semantics. -/
theorem flatQuantum_correct {n m : Nat} (c : List (Instruction n m)) (ψ : QuantumState n m) :
    ShiShallow.runLayered (substitute (c.map flatInstruction))
      (fun x => ψ ((registerEquiv n m).symm x)) =
      fun x => quantumRun c ψ ((registerEquiv n m).symm x) := by
  rw [substitute_correct]
  funext x
  have h := flatProgram_correct c.reverse ((registerEquiv n m).symm x)
  rw [List.map_reverse, Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]
  rfl

end ShiReversibleGateBridge
