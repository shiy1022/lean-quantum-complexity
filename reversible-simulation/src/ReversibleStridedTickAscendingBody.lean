import ReversibleStridedTickDescendingTraversal
import ReversibleIncrementProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def stridedTickAscendingBody (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) :=
  sequenceProgramTemplate (stridedTickCoordinateBody tm kind inputStride bound backward)
    (incrementProgramTemplate (.inl 2))

theorem stridedTickAscendingBody_embeds (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) :
    (stridedTickAscendingBody tm kind inputStride bound backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (stridedTickCoordinateBody_embeds tm kind inputStride bound backward)
    (incrementProgramTemplate_embeds _)

theorem stridedTickAscendingBody_run (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) :
    (stridedTickAscendingBody tm kind inputStride bound backward).Runs :=
  sequenceProgramTemplate_run _ _ (stridedTickCoordinateBody_embeds tm kind inputStride bound backward)
    (stridedTickCoordinateBody_run tm kind inputStride bound backward) (incrementProgramTemplate_run _)

theorem stridedTickAscendingBody_ready (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    (stridedTickAscendingBody tm kind inputStride bound backward).ready cs :=
  ⟨stridedTickCoordinateBody_ready tm kind inputStride bound backward cs hr, trivial⟩

theorem stridedTickAscendingBody_position (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (stridedTickAscendingBody tm kind inputStride bound backward).counters cs (.inl 2) = cs (.inl 2) + 1 := by
  let after := (stridedTickCoordinateBody tm kind inputStride bound backward).counters cs
  change Function.update after (.inl 2) (after (.inl 2) + 1) (.inl 2) = _
  rw [Function.update_self]
  dsimp only [after]
  rw [stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs 2 (by decide)]

theorem stridedTickAscendingBody_capacity (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (stridedTickAscendingBody tm kind inputStride bound backward).counters cs (.inl 1) = cs (.inl 1) := by
  let after := (stridedTickCoordinateBody tm kind inputStride bound backward).counters cs
  change Function.update after (.inl 2) (after (.inl 2) + 1) (.inl 1) = _
  rw [Function.update_of_ne (by simp : (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 2)]
  exact stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs 1 (by decide)

theorem stridedTickAscendingBody_spare_frame (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (stridedTickAscendingBody tm kind inputStride bound backward).counters cs (tickTraversalSpare tm j) =
      cs (tickTraversalSpare tm j) := by
  let after := (stridedTickCoordinateBody tm kind inputStride bound backward).counters cs
  change Function.update after (.inl 2) (after (.inl 2) + 1) (tickTraversalSpare tm j) = _
  rw [Function.update_of_ne (by simp [tickTraversalSpare])]
  exact stridedTickCoordinateBody_spare_frame tm kind inputStride bound backward cs j

theorem stridedTickAscendingBody_ready_preserved (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm)
      ((stridedTickAscendingBody tm kind inputStride bound backward).counters cs) := by
  have h := stridedTickCoordinateBody_ready_preserved tm kind inputStride bound backward cs hr
  simpa [stridedTickAscendingBody, sequenceProgramTemplate, incrementProgramTemplate, fixedGuardedEmitterReady] using h

theorem stridedTickAscendingBody_polynomial (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride strideBound : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (stridedTickAscendingBody tm kind inputStride strideBound backward).PolynomiallyTimed bound := by
  obtain ⟨clock, hc⟩ := stridedTickCoordinateBody_polynomial tm kind inputStride strideBound backward bound
  refine ⟨clock + 1, ?_⟩
  intro n cs hb hr
  simpa only [stridedTickAscendingBody, sequenceProgramTemplate, incrementProgramTemplate,
    Polynomial.eval_add, Polynomial.eval_one] using Nat.add_le_add_right (hc n cs hb hr.1) 1

end ShiReversibleGenerator
