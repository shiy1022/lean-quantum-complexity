import ReversibleStridedTickCoordinateBody
import ReversibleTickCoordinateFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem stridedTickCoordinateBody_control_frame (tm : Turing.FinTM2) (kind : TickTreeKind tm) (inputStride : Nat) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (stridedTickCoordinateBody tm kind inputStride bound backward).counters cs (.inl q) = cs (.inl q) := by
  change (stridedSharedFixedGuardedEmitter (tickTraversalSupply tm) (tickTreeForKind tm kind) inputStride backward).counters
    (tickOutputPreparationCounters tm kind bound cs) (.inl q) = _
  rw [stridedSharedFixedGuardedEmitter_control_frame _ _ _ _ _ q ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩]
  simp [tickOutputPreparationCounters, hq.2.2.2.2.1, hq.2.2.2.2.2]

theorem stridedTickCoordinateBody_ready_preserved (tm : Turing.FinTM2) (kind : TickTreeKind tm) (inputStride : Nat) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (h : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((stridedTickCoordinateBody tm kind inputStride bound backward).counters cs) := by
  unfold fixedGuardedEmitterReady at h ⊢
  rcases h with ⟨h3, h4, h5, h10, h11⟩
  have hf := stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hf 3 (by decide)]; exact h3
  · rw [hf 4 (by decide)]; exact h4
  · rw [hf 5 (by decide)]; exact h5
  · rw [hf 10 (by decide)]; exact h10
  · rw [hf 11 (by decide)]; exact h11


end ShiReversibleGenerator
