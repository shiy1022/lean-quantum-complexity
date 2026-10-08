import ReversibleTickStackTraversalTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem TickWindowBudget.remaining_update (tm : Turing.FinTM2) (inputStride strideBound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (k : Nat)
    (h : TickWindowBudget tm inputStride strideBound wireBound cs) :
    TickWindowBudget tm inputStride strideBound wireBound (Function.update cs (tickTraversalSpare tm 0) k) := by
  simpa [TickWindowBudget,tickTraversalSpare,Fin.ext_iff] using h

theorem fixedGuardedEmitterReady_position_update (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (k : Nat)
    (h : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) (Function.update cs (.inl 2) k) := by
  simpa [fixedGuardedEmitterReady] using h

theorem fixedGuardedEmitterReady_remaining_update (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (k : Nat)
    (h : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) (Function.update cs (tickTraversalSpare tm 0) k) := by
  simpa [fixedGuardedEmitterReady,tickTraversalSpare] using h

/-- Copying the stored capacity initializes the actual descending traversal invariant. -/
theorem tickDescendingStackSetup_invariant (tm : Turing.FinTM2) (inputStride strideBound wireBound layers increment : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) {L : Type}
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hl : cs (.inl 9) ≤ layers) :
    TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers (cs (.inl 1)) increment (cs (.inl 1))
      (⟨none,(counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs,[]⟩ : CounterCfg _ L) := by
  let after := Function.update cs (Sum.inl 2 : FixedLeafRegister (tickTraversalSupply tm)) (cs (.inl 1))
  have ha := fixedGuardedEmitterReady_position_update tm cs (cs (.inl 1)) hr
  have hab := hb.update (.inl 2) (cs (.inl 1)) (hb (.inl 1) (by simp))
  have haw := TickWindowBudget.position_update tm inputStride strideBound wireBound cs (cs (.inl 1)) hw
  change TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers (cs (.inl 1)) increment (cs (.inl 1))
    (⟨none,after,[]⟩ : CounterCfg _ L)
  refine ⟨⟨ha,by simp [after],le_rfl⟩,hab,haw,?_⟩
  simpa [after] using hl

/-- Clear position, then copy capacity to the separate remaining counter for reverse emission. -/
theorem tickAscendingStackSetup_invariant (tm : Turing.FinTM2) (inputStride strideBound wireBound layers increment : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) {L : Type}
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hl : cs (.inl 9) ≤ layers) :
    TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers (cs (.inl 1)) increment (cs (.inl 1))
      (⟨none,(counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters
        ((cleanupProgramTemplate [.inl 2]).counters cs),[]⟩ : CounterCfg _ L) := by
  let cleared := Function.update cs (Sum.inl 2 : FixedLeafRegister (tickTraversalSupply tm)) 0
  let after := Function.update cleared (tickTraversalSpare tm 0) (cs (.inl 1))
  have hz := fixedGuardedEmitterReady_position_update tm cs 0 hr
  have ha := fixedGuardedEmitterReady_remaining_update tm cleared (cs (.inl 1)) hz
  have hzb := hb.update (.inl 2) 0 (Nat.zero_le _)
  have hab := hzb.update (tickTraversalSpare tm 0) (cs (.inl 1)) (hb (.inl 1) (by simp))
  have hzw := TickWindowBudget.position_update tm inputStride strideBound wireBound cs 0 hw
  have haw := TickWindowBudget.remaining_update tm inputStride strideBound wireBound cleared (cs (.inl 1)) hzw
  change TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers (cs (.inl 1)) increment (cs (.inl 1))
    (⟨none,Function.update cleared (tickTraversalSpare tm 0) (cleared (.inl 1)),[]⟩ : CounterCfg _ L)
  have hc : cleared (.inl 1)=cs (.inl 1) := by simp [cleared]
  rw [hc]
  refine ⟨⟨ha,by simp [after,cleared,tickTraversalSpare],by simp [after,cleared,tickTraversalSpare]⟩,hab,haw,?_⟩
  simpa [after,cleared,tickTraversalSpare] using hl

end ShiReversibleGenerator
