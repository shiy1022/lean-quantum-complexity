import «BQP-gate-semantics»

/-! Executable path data shared by amplitude counting and program simulation.
The uniqueness lemmas identify witnesses obtained from the recovered existence
proofs with these concrete recursions. -/
set_option autoImplicit false

namespace BQPPaths
open ShiShallow BQPGates

def phaseStep {n : ℕ} (g : Instr n) (a : Bool) (z : Bits n) : ZMod 8 :=
  match g with
  | .h i => if z i && a then 4 else 0
  | .s i => if z i then 2 else 0
  | .t i => if z i then 1 else 0
  | _ => 0

def forwardRun {n : ℕ} : List (Instr n) → Bits n → List Bool → Bits n
  | [], z, _ => z
  | .h i :: gs, z, w => forwardRun gs (forward (.h i) w.headI z) w.tail
  | g :: gs, z, w => forwardRun gs (forward g false z) w

def phaseRun {n : ℕ} : List (Instr n) → Bits n → List Bool → ZMod 8
  | [], _, _ => 0
  | .h i :: gs, z, w =>
      phaseStep (.h i) w.headI z + phaseRun gs (forward (.h i) w.headI z) w.tail
  | g :: gs, z, w => phaseStep g false z + phaseRun gs (forward g false z) w

def backwardWitness {n : ℕ} : List (Instr n) → Bits n → List Bool → List Bool
  | [], _, _ => []
  | .h i :: gs, z, w => z i :: backwardWitness gs (forward (.h i) w.headI z) w.tail
  | g :: gs, z, w => backwardWitness gs (forward g false z) w

def hadamardCount {n : ℕ} (gs : List (Instr n)) : ℕ :=
  gs.countP (fun g => match g with | .h _ => true | _ => false)

theorem backwardWitness_length {n : ℕ} (gs : List (Instr n)) (z : Bits n) (w : List Bool) :
    (backwardWitness gs z w).length = hadamardCount gs := by
  induction gs generalizing z w with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [backwardWitness, hadamardCount, ih, Nat.add_comm]

theorem forwardRun_unique {n : ℕ}
    (F : List (Instr n) → Bits n → List Bool → Bits n)
    (h0 : ∀ z w, F [] z w = z)
    (hh : ∀ i gs z w, F (.h i :: gs) z w = F gs (forward (.h i) w.headI z) w.tail)
    (hg : ∀ g gs z w, (∀ i, g ≠ Instr.h i) →
      F (g :: gs) z w = F gs (forward g false z) w) :
    ∀ gs z w, F gs z w = forwardRun gs z w := by
  intro gs
  induction gs with
  | nil => exact h0
  | cons g gs ih =>
      intro z w
      cases g with
      | h i => rw [hh]; exact ih _ _
      | s i => rw [hg _ _ _ _ (by intro j; simp)]; exact ih _ _
      | t i => rw [hg _ _ _ _ (by intro j; simp)]; exact ih _ _
      | x i => rw [hg _ _ _ _ (by intro j; simp)]; exact ih _ _
      | cnot i j hij => rw [hg _ _ _ _ (by intro k; simp)]; exact ih _ _

theorem phaseRun_unique {n : ℕ}
    (P : List (Instr n) → Bits n → List Bool → ZMod 8)
    (h0 : ∀ z w, P [] z w = 0)
    (hh : ∀ i gs z w, P (.h i :: gs) z w =
      phaseStep (.h i) w.headI z + P gs (forward (.h i) w.headI z) w.tail)
    (hg : ∀ g gs z w, (∀ i, g ≠ Instr.h i) →
      P (g :: gs) z w = phaseStep g false z + P gs (forward g false z) w) :
    ∀ gs z w, P gs z w = phaseRun gs z w := by
  intro gs
  induction gs with
  | nil => exact h0
  | cons g gs ih =>
      intro z w
      cases g with
      | h i => rw [hh, ih]; rfl
      | s i => rw [hg _ _ _ _ (by intro j; simp), ih]; rfl
      | t i => rw [hg _ _ _ _ (by intro j; simp), ih]; rfl
      | x i => rw [hg _ _ _ _ (by intro j; simp), ih]; rfl
      | cnot i j hij => rw [hg _ _ _ _ (by intro k; simp), ih]; rfl

end BQPPaths
