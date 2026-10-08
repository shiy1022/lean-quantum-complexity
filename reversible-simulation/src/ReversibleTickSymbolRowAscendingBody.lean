import ReversibleTickSymbolRowDescendingTraversal
import ReversibleIncrementProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickSymbolRowAscendingBody (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) :=
  sequenceProgramTemplate (tickSymbolRowTemplate tm stack inputStride bound backward)
    (incrementProgramTemplate (.inl 2))

theorem tickSymbolRowAscendingBody_embeds (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) :
    (tickSymbolRowAscendingBody tm stack inputStride bound backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickSymbolRowTemplate_embeds tm stack inputStride bound backward)
    (incrementProgramTemplate_embeds _)

theorem tickSymbolRowAscendingBody_run (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) :
    (tickSymbolRowAscendingBody tm stack inputStride bound backward).Runs :=
  sequenceProgramTemplate_run _ _ (tickSymbolRowTemplate_embeds tm stack inputStride bound backward)
    (tickSymbolRowTemplate_run tm stack inputStride bound backward) (incrementProgramTemplate_run _)

theorem tickSymbolRowAscendingBody_ready (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    (tickSymbolRowAscendingBody tm stack inputStride bound backward).ready cs :=
  ⟨tickSymbolRowTemplate_ready tm stack inputStride bound backward cs hr, trivial⟩

theorem tickSymbolRowAscendingBody_position (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowAscendingBody tm stack inputStride bound backward).counters cs (.inl 2) = cs (.inl 2) + 1 := by
  let after := (tickSymbolRowTemplate tm stack inputStride bound backward).counters cs
  change Function.update after (.inl 2) (after (.inl 2) + 1) (.inl 2) = _
  rw [Function.update_self]
  dsimp only [after]
  rw [tickSymbolRowTemplate_control_frame tm stack inputStride bound backward cs 2 (by decide)]

theorem tickSymbolRowAscendingBody_capacity (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowAscendingBody tm stack inputStride bound backward).counters cs (.inl 1) = cs (.inl 1) := by
  let after := (tickSymbolRowTemplate tm stack inputStride bound backward).counters cs
  change Function.update after (.inl 2) (after (.inl 2) + 1) (.inl 1) = _
  rw [Function.update_of_ne (by simp : (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 2)]
  exact tickSymbolRowTemplate_control_frame tm stack inputStride bound backward cs 1 (by decide)

theorem tickSymbolRowAscendingBody_spare_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (tickSymbolRowAscendingBody tm stack inputStride bound backward).counters cs (tickTraversalSpare tm j) =
      cs (tickTraversalSpare tm j) := by
  let after := (tickSymbolRowTemplate tm stack inputStride bound backward).counters cs
  change Function.update after (.inl 2) (after (.inl 2) + 1) (tickTraversalSpare tm j) = _
  rw [Function.update_of_ne (by simp [tickTraversalSpare])]
  exact tickSymbolRowTemplate_spare_frame tm stack inputStride bound backward cs j

theorem tickSymbolRowAscendingBody_ready_preserved (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm)
      ((tickSymbolRowAscendingBody tm stack inputStride bound backward).counters cs) := by
  have h := tickSymbolRowTemplate_ready_preserved tm stack inputStride bound backward cs hr
  simpa [tickSymbolRowAscendingBody, sequenceProgramTemplate, incrementProgramTemplate, fixedGuardedEmitterReady] using h

theorem tickSymbolRowAscendingBody_polynomial (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (tickSymbolRowAscendingBody tm stack inputStride strideBound backward).PolynomiallyTimed bound := by
  obtain ⟨clock, hc⟩ := tickSymbolRowTemplate_polynomial tm stack inputStride strideBound backward bound
  refine ⟨clock + 1, ?_⟩
  intro n cs hb hr
  simpa only [tickSymbolRowAscendingBody, sequenceProgramTemplate, incrementProgramTemplate,
    Polynomial.eval_add, Polynomial.eval_one] using Nat.add_le_add_right (hc n cs hb hr.1) 1

end ShiReversibleGenerator
