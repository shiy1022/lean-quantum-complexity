import ReversibleArithmeticSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

/-- Bind the relocated configuration coordinate using only fixed coefficients. -/
def cellAddressAtoms (input capacity index target : R) (offset rank stride : Nat) : List (AffineAtom R) :=
  [⟨input, target, offset, 1⟩, ⟨capacity, target, 0, rank * stride⟩, ⟨index, target, 0, stride⟩]

theorem cellAddressAtoms_valid (input capacity index target tmp : R) (offset rank stride : Nat)
    (hit : input ≠ target) (hct : capacity ≠ target) (hjt : index ≠ target)
    (hix : input ≠ tmp) (hcx : capacity ≠ tmp) (hjx : index ≠ tmp) (htx : target ≠ tmp) :
    ∀ a ∈ cellAddressAtoms input capacity index target offset rank stride, a.Valid tmp := by
  simp [cellAddressAtoms, AffineAtom.Valid, hit, hct, hjt, hix, hcx, hjx, htx]

theorem cellAddressAtoms_result (input capacity index target : R) (offset rank stride : Nat)
    (hit : input ≠ target) (hct : capacity ≠ target) (hjt : index ≠ target) (cs : R → Nat) :
    arithmeticResult (cellAddressAtoms input capacity index target offset rank stride) cs =
      Function.update cs target (cs target + cs input + offset + (rank * stride) * cs capacity + stride * cs index) := by
  simp [cellAddressAtoms, arithmeticResult, AffineAtom.apply, hit, hct, hjt, Nat.add_assoc]

theorem cellAddressAtoms_steps (input capacity index target : R) (offset rank stride : Nat)
    (hct : capacity ≠ target) (hjt : index ≠ target) (cs : R → Nat) :
    arithmeticSteps (cellAddressAtoms input capacity index target offset rank stride) cs =
      ((7 * cs input + 2) + offset) + ((rank * stride) * (7 * cs capacity + 2)) +
        (stride * (7 * cs index + 2)) := by
  simp [cellAddressAtoms, arithmeticSteps, AffineAtom.steps, AffineAtom.apply, hct, hjt, Nat.add_assoc]

end ShiReversibleGenerator
