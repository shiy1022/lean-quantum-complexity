import ReversibleDescendingProgramTemplate
import ReversibleDescendingTemplateReadyInvariant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickSymbolRowAscendingTemplate (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :=
  descendingProgramTemplate (tickSymbolRowAscendingBody tm stack inputStride strideBound backward) (tickTraversalSpare tm 0)

theorem tickSymbolRowAscendingTemplate_embeds (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).Embeds :=
  descendingProgramTemplate_embeds _ _ (tickSymbolRowAscendingBody_embeds tm stack inputStride strideBound backward)

theorem tickSymbolRowAscendingTemplate_run (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).Runs :=
  descendingProgramTemplate_run _ _ (tickSymbolRowAscendingBody_embeds tm stack inputStride strideBound backward)
    (tickSymbolRowAscendingBody_run tm stack inputStride strideBound backward)

theorem tickSymbolRowAscendingTemplate_ready (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (cs (tickTraversalSpare tm 0))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).Labels (Fin 3)))) :
    (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).ready cs := by
  let p := tickSymbolRowAscendingBody tm stack inputStride strideBound backward
  change descendingTemplateReady p (tickTraversalSpare tm 0) (cs (tickTraversalSpare tm 0)) cs
  refine descendingTemplateReady_of_invariant p (tickTraversalSpare tm 0)
    (fun k (t : CounterCfg _ (p.Labels (Fin 3))) => TickAscendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) k t) ?_ ?_ ?_ (cs (tickTraversalSpare tm 0)) ⟨none,cs,[]⟩ hs
  · intro k t ht
    apply tickSymbolRowAscendingBody_ready
    simpa [tickTraversalSpare,fixedGuardedEmitterReady] using ht.1.1
  · intro k t ht
    rw [tickSymbolRowAscendingBody_spare_frame tm stack inputStride strideBound backward _ 0]
    simp
  · intro k t ht
    exact tickSymbolRowAscendingBudget_next tm stack inputStride strideBound backward
      wireBound layers capacity k t hsize ht

theorem tickSymbolRowAscendingTemplate_clock (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      TickAscendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
        ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (cs (tickTraversalSpare tm 0))
        (⟨none,cs,[]⟩ : CounterCfg _ ((tickSymbolRowAscendingBody tm stack inputStride strideBound backward).Labels (Fin 3))) →
      (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).steps cs ≤ clock.eval n := by
  obtain ⟨clock,hclock⟩ := tickSymbolRowAscendingTraversal_polynomial tm stack inputStride strideBound backward
    capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n cs hs
  let p := tickSymbolRowAscendingBody tm stack inputStride strideBound backward
  let s : CounterCfg _ (p.Labels (Fin 3)) := ⟨none,cs,[]⟩
  have h := hclock n (cs (tickTraversalSpare tm 0)) s hs
  change descendingSteps (templateDescendingBody p (tickTraversalSpare tm 0))
    (templateDescendingCost p (tickTraversalSpare tm 0)) (cs (tickTraversalSpare tm 0)) s ≤ _ at h
  rw [descendingTemplateSteps_eq] at h
  exact h

end ShiReversibleGenerator
