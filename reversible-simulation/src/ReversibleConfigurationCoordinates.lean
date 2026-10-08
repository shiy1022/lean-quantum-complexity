import ReversibleConfigurationBits

set_option autoImplicit false
namespace ShiReversibleTM
open ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- The cell coordinate has fixed machine ranks and only affine capacity/index dependence. -/
theorem configurationBitEquiv_cell_val (tm : Turing.FinTM2) (capacity : Nat)
    (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm)) :
    (configurationBitEquiv tm capacity (.inr ((k, i), a))).val =
      Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
        (((Fintype.equivFin tm.K) k).val * capacity + i.val) *
          Fintype.card (Option (MachineSymbol tm)) +
        ((Fintype.equivFin (Option (MachineSymbol tm))) a).val := by
  classical
  change (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) +
    (((Fintype.equivFin (Option (MachineSymbol tm))) a).val +
      Fintype.card (Option (MachineSymbol tm)) *
        (i.val + capacity * ((Fintype.equivFin tm.K) k).val)) = _
  ring

theorem configurationBitEquiv_label_val (tm : Turing.FinTM2) (capacity : Nat)
    (l : Option tm.Λ) :
    (configurationBitEquiv tm capacity (.inl (.inl l))).val =
      ((Fintype.equivFin (Option tm.Λ)) l).val := by
  classical
  rfl

theorem configurationBitEquiv_memory_val (tm : Turing.FinTM2) (capacity : Nat)
    (v : tm.σ) :
    (configurationBitEquiv tm capacity (.inl (.inr v))).val =
      Fintype.card (Option tm.Λ) + ((Fintype.equivFin tm.σ) v).val := by
  classical
  rfl

end ShiReversibleTM
