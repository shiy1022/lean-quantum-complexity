import ReversibleStridedCoordinateBindingBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- Address budgets depend only on the three real source counters, independent of old fields. -/
theorem stridedTickCoordinateAddress_source_polynomial (tm : Turing.FinTM2)
    (env : CoordinateBindingRegisters R) (stride : Nat) (coordinate : TickSymbolicCoordinate tm)
    (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : R → Nat),
      cs env.input ≤ bound.eval n → cs env.capacity ≤ bound.eval n → cs env.position ≤ bound.eval n →
      stridedTickCoordinateAddress tm env stride coordinate cs ≤ budget.eval n := by
  obtain ⟨budget,h⟩ := stridedTickCoordinateAddress_polynomial tm env stride coordinate bound
  refine ⟨budget,?_⟩
  intro n cs hi hc hp
  let capped : R → Nat := fun q => min (cs q) (bound.eval n)
  have hb : ∀ q,capped q ≤ bound.eval n := fun q => Nat.min_le_right _ _
  have he : stridedTickCoordinateAddress tm env stride coordinate capped =
      stridedTickCoordinateAddress tm env stride coordinate cs := by
    simp only [stridedTickCoordinateAddress,capped,Nat.min_eq_left hi,Nat.min_eq_left hc,Nat.min_eq_left hp]
  rw [← he]
  exact h n capped hb

end ShiReversibleGenerator
