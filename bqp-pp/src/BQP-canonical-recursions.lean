import «BQP-canonical-paths»

set_option autoImplicit false
namespace BQPPaths
open ShiShallow BQPGates

@[simp] theorem hadamardCount_reverse {n : ℕ} (gs : List (Instr n)) :
    hadamardCount gs.reverse = hadamardCount gs := by
  simp [hadamardCount]

/-- Extra witness bits are untouched by either the state or phase recursion.
This supplies the prefix interface required by the doubled-program proof. -/
theorem canonical_witness_prefix {n : ℕ} (gs : List (Instr n))
    (z : Bits n) (w u : List Bool) (hw : hadamardCount gs ≤ w.length) :
    forwardRun gs z (w ++ u) = forwardRun gs z w ∧
      phaseRun gs z (w ++ u) = phaseRun gs z w := by
  induction gs generalizing z w with
  | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih =>
    cases g with
    | h i =>
      cases w with
      | nil => simp [hadamardCount] at hw
      | cons a w =>
        have ht : hadamardCount gs ≤ w.length := by simpa [hadamardCount] using hw
        obtain ⟨hs, hp⟩ := ih (forward (.h i) a z) w ht
        simp [forwardRun, phaseRun, hs, hp]
    | s i =>
      have ht : hadamardCount gs ≤ w.length := by simpa [hadamardCount] using hw
      obtain ⟨hs, hp⟩ := ih (forward (.s i) false z) w ht
      simp only [forwardRun, phaseRun, hs, hp, and_self]
    | t i =>
      have ht : hadamardCount gs ≤ w.length := by simpa [hadamardCount] using hw
      obtain ⟨hs, hp⟩ := ih (forward (.t i) false z) w ht
      simp only [forwardRun, phaseRun, hs, hp, and_self]
    | x i =>
      have ht : hadamardCount gs ≤ w.length := by simpa [hadamardCount] using hw
      obtain ⟨hs, hp⟩ := ih (forward (.x i) false z) w ht
      simp only [forwardRun, phaseRun, hs, hp, and_self]
    | cnot i j hij =>
      have ht : hadamardCount gs ≤ w.length := by simpa [hadamardCount] using hw
      obtain ⟨hs, hp⟩ := ih (forward (.cnot i j hij) false z) w ht
      simp only [forwardRun, phaseRun, hs, hp, and_self]

end BQPPaths
