import ReversibleConfigurationHeaderPayload
import ReversibleConstantSequenceControl
import ReversibleInitializationSchema

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding ShiReversibleFormula
open scoped Classical
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def initializationConstantRanks (tm : Turing.FinTM2) : List (Bool × Nat) :=
  List.ofFn (fun j : Fin (Fintype.card (Option (MachineSymbol tm))) =>
    (oneHot none ((Fintype.equivFin (Option (MachineSymbol tm))).symm j), j.val))

noncomputable def initializationConstantSchedule (tm : Turing.FinTM2) (backward : Bool) :=
  if backward then initializationConstantRanks tm else (initializationConstantRanks tm).reverse

theorem initializationConstantSchedule_rank_bound (tm : Turing.FinTM2) (backward : Bool)
    (ar : Bool × Nat) (h : ar ∈ initializationConstantSchedule tm backward) :
    ar.2 < Fintype.card (Option (MachineSymbol tm)) := by
  have hr : ar ∈ initializationConstantRanks tm := by
    cases backward <;> simpa [initializationConstantSchedule] using h
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact i.isLt

/-- Other stacks use the same constant schema at their exact machine-rank coordinates. -/
theorem constantStack_coordinate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (i : Fin capacity) (a : Option (MachineSymbol tm))
    (hk : k ≠ tm.k₀) (backward : Bool) :
    constantInitializationPayload (oneHot none a) backward
      (n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
        (((Fintype.equivFin tm.K) k).val * capacity + i.val) *
          Fintype.card (Option (MachineSymbol tm)) +
        ((Fintype.equivFin (Option (MachineSymbol tm))) a).val)) =
    initializationFormulaPayload ((initialFormulas tm e capacity n).cells k i a) backward
      (n + 18 * (configurationBitEquiv tm capacity (.inr ((k, i), a))).val) := by
  rw [initialFormulas_padding_cell_schema tm e capacity n k i a (Or.inl hk),
    configurationBitEquiv_cell_val]
  cases a <;> simp [oneHot, initializationFormulaPayload, constantInitializationPayload, Formula.paddedCompile,
    Formula.rawCompile, Formula.size, Formula.result]

/-- Ranked finite constant dispatch prints exactly its listed symbol coordinates. -/
theorem constantStack_rank_payload (tm : Turing.FinTM2) (capacity n index stackRank : Nat)
    (backward : Bool) :
    constantCellPayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
      (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantRanks tm)
      capacity n index =
    (initializationConstantRanks tm).reverse.flatMap (fun ar =>
      constantInitializationPayload ar.1 backward
        (n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
          (stackRank * capacity + index) * Fintype.card (Option (MachineSymbol tm)) + ar.2))) := by
  rfl

theorem constantStack_schedule_payload (tm : Turing.FinTM2) (capacity n index stackRank : Nat)
    (backward : Bool) :
    constantCellPayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank
      (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)
      capacity n index =
    (if backward then (initializationConstantRanks tm).reverse else initializationConstantRanks tm).flatMap
      (fun ar => constantInitializationPayload ar.1 backward
        (n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
          (stackRank * capacity + index) * Fintype.card (Option (MachineSymbol tm)) + ar.2))) := by
  cases backward <;> simp [constantCellPayload, initializationConstantSchedule]

end ShiReversibleGenerator
