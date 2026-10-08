import ReversibleDescendingTemplateCounterResult

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickCoordinateListDescendingTemplate_final_bounds (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) (cs (.inl 2))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3)))) :
    let final := (tickCoordinateListDescendingTemplate tm kinds inputStride strideBound backward).counters cs
    CounterBudget final (.inl 9) wireBound ∧ TickWindowBudget tm inputStride strideBound wireBound final ∧
      fixedGuardedEmitterReady (tickTraversalSupply tm) final ∧
      final (.inl 9) ≤ layers+capacity*(kinds.length*(37*tickSizeBound tm+1)) := by
  let p := tickCoordinateListTemplate tm kinds inputStride strideBound backward
  let s : CounterCfg _ (p.Labels (Fin 3)) := ⟨none,cs,[]⟩
  let result := descendingResult (templateDescendingBody p (.inl 2)) (cs (.inl 2)) s
  have h := tickCoordinateListDescendingTraversal_final_budget tm kinds inputStride strideBound backward
    wireBound layers capacity (cs (.inl 2)) s hsize hs
  have he : programDescendingBody p (.inl 2) =
      (templateDescendingBody p (.inl 2) : Nat → CounterCfg _ (p.Labels (Fin 3)) → CounterCfg _ (p.Labels (Fin 3))) := rfl
  rw [he] at h
  have hb : CounterBudget result.counters (.inl 9) wireBound := h.2.1
  have hw : TickWindowBudget tm inputStride strideBound wireBound result.counters := h.2.2.1
  have hr : fixedGuardedEmitterReady (tickTraversalSupply tm) result.counters := h.1.1
  have hl : result.counters (.inl 9) ≤ layers+capacity*(kinds.length*(37*tickSizeBound tm+1)) := by
    simpa only [Nat.sub_zero,result,p,programDescendingBody,templateDescendingBody] using h.2.2.2
  dsimp only [tickCoordinateListDescendingTemplate]
  rw [descendingProgramTemplate_result_counters p (.inl 2) cs [] (none : Option (p.Labels (Fin 3)))]
  refine ⟨hb.update (.inl 2) 0 (Nat.zero_le _),
    TickWindowBudget.position_update tm inputStride strideBound wireBound result.counters 0 hw,
    fixedGuardedEmitterReady_position_update tm result.counters 0 hr,?_⟩
  simpa only [Function.update_of_ne (by simp : (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 2)] using hl

end ShiReversibleGenerator
