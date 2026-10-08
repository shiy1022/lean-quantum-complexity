import ReversibleDescendingTemplateCounterResult

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowAscendingTemplate_final_bounds (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (cs (tickTraversalSpare tm 0))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).Labels (Fin 3)))) :
    let final := (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).counters cs
    CounterBudget final (.inl 9) wireBound ∧ TickWindowBudget tm inputStride strideBound wireBound final ∧
      fixedGuardedEmitterReady (tickTraversalSupply tm) final ∧
      final (.inl 9) ≤ layers+capacity*((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) := by
  let p := tickSymbolRowAscendingBody tm stack inputStride strideBound backward
  let s : CounterCfg _ (p.Labels (Fin 3)) := ⟨none,cs,[]⟩
  let remaining := tickTraversalSpare tm 0
  let result := descendingResult (templateDescendingBody p remaining) (cs remaining) s
  have h := tickSymbolRowAscendingTraversal_final_budget tm stack inputStride strideBound backward
    wireBound layers capacity (cs remaining) s hsize hs
  have he : programDescendingBody p remaining =
      (templateDescendingBody p remaining : Nat → CounterCfg _ (p.Labels (Fin 3)) → CounterCfg _ (p.Labels (Fin 3))) := rfl
  rw [he] at h
  have hb : CounterBudget result.counters (.inl 9) wireBound := h.2.1
  have hw : TickWindowBudget tm inputStride strideBound wireBound result.counters := h.2.2.1
  have hr : fixedGuardedEmitterReady (tickTraversalSupply tm) result.counters := h.1.1
  have hl : result.counters (.inl 9) ≤ layers+capacity*((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) := by
    simpa only [Nat.sub_zero,result,p,remaining,programDescendingBody,templateDescendingBody] using h.2.2.2
  dsimp only [tickSymbolRowAscendingTemplate]
  rw [descendingProgramTemplate_result_counters p remaining cs [] (none : Option (p.Labels (Fin 3)))]
  refine ⟨hb.update remaining 0 (Nat.zero_le _),
    TickWindowBudget.remaining_update tm inputStride strideBound wireBound result.counters 0 hw,
    fixedGuardedEmitterReady_remaining_update tm result.counters 0 hr,?_⟩
  simpa only [Function.update_of_ne (by simp [remaining,tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ remaining)] using hl

end ShiReversibleGenerator
