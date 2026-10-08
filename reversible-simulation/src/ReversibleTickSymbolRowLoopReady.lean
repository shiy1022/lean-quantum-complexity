import ReversibleTickStackSetupInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowDescendingTemplate_ready (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (cs (.inl 2))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickSymbolRowTemplate tm stack inputStride strideBound backward).Labels (Fin 3)))) :
    (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)).ready cs := by
  let kinds := if backward then tickSymbolRowKinds tm stack else (tickSymbolRowKinds tm stack).reverse
  have hs' : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) (cs (.inl 2))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3))) := by
    cases backward <;> simpa only [kinds,tickSymbolRowTemplate,Bool.false_eq_true,if_false,if_true,List.length_reverse] using hs
  exact tickCoordinateListDescendingTemplate_ready tm kinds inputStride strideBound backward wireBound layers capacity cs hsize hs'

theorem tickSymbolRowDescendingTemplate_clock (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      TickDescendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
        ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (cs (.inl 2))
        (⟨none,cs,[]⟩ : CounterCfg _ ((tickSymbolRowTemplate tm stack inputStride strideBound backward).Labels (Fin 3))) →
      (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)).steps cs ≤ clock.eval n := by
  obtain ⟨clock,hclock⟩ := tickSymbolRowDescendingTraversal_polynomial tm stack inputStride strideBound backward
    capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n cs hs
  let p := tickSymbolRowTemplate tm stack inputStride strideBound backward
  let s : CounterCfg _ (p.Labels (Fin 3)) := ⟨none,cs,[]⟩
  have h := hclock n (cs (.inl 2)) s hs
  change descendingSteps (templateDescendingBody p (.inl 2)) (templateDescendingCost p (.inl 2)) (cs (.inl 2)) s ≤ _ at h
  rw [descendingTemplateSteps_eq] at h
  exact h

end ShiReversibleGenerator
