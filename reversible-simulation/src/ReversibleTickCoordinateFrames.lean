import ReversibleTickCoordinateBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem tickCoordinateBody_control_frame (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickCoordinateBody tm kind bound backward).counters cs (.inl q) = cs (.inl q) := by
  change (sharedFixedGuardedEmitter (tickTraversalSupply tm) (tickTreeForKind tm kind) backward).counters
    (tickOutputPreparationCounters tm kind bound cs) (.inl q) = _
  rw [sharedFixedGuardedEmitter_control_frame _ _ _ _ q ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩]
  simp [tickOutputPreparationCounters, hq.2.2.2.2.1, hq.2.2.2.2.2]

theorem tickCoordinateBody_ready_preserved (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (h : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((tickCoordinateBody tm kind bound backward).counters cs) := by
  unfold fixedGuardedEmitterReady at h ⊢
  rcases h with ⟨h3, h4, h5, h10, h11⟩
  have hf := tickCoordinateBody_control_frame tm kind bound backward cs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hf 3 (by decide)]; exact h3
  · rw [hf 4 (by decide)]; exact h4
  · rw [hf 5 (by decide)]; exact h5
  · rw [hf 10 (by decide)]; exact h10
  · rw [hf 11 (by decide)]; exact h11

def tickKindBit (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity) : TickTreeKind tm → ConfigurationBit tm capacity
  | .inl z => .inl z
  | .inr (k, a) => .inr ((k, i), a)

/-- Prepared output addresses are exactly the fixed-stride forest compiler's established coordinate addresses. -/
theorem tickPreparedOutputAddress_coordinate (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    tickPreparedOutputAddress tm kind bound cs = cs (tickTraversalSpare tm 2) +
      (configurationBitEquiv tm (cs (.inl 1)) (tickKindBit tm (cs (.inl 1)) ⟨cs (.inl 2), hi⟩ kind)).val * (bound + 1) := by
  cases kind with
  | inl z => cases z with
    | inl l =>
      simp [tickPreparedOutputAddress, symbolicCellAddress, TickIndexExpr.eval, tickOutputAddressParameters,
        tickKindBit, configurationBitEquiv_label_val]
    | inr v =>
      simp [tickPreparedOutputAddress, symbolicCellAddress, TickIndexExpr.eval, tickOutputAddressParameters,
        tickKindBit, configurationBitEquiv_memory_val]
  | inr z =>
    simp only [tickPreparedOutputAddress, symbolicCellAddress, TickIndexExpr.eval, tickOutputAddressParameters,
      tickKindBit, configurationBitEquiv_cell_val]
    ring

end ShiReversibleGenerator
