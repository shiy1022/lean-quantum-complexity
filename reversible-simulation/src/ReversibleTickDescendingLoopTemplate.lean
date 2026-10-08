import ReversibleDescendingProgramTemplate
import ReversibleDescendingTemplateReadyInvariant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickCoordinateListDescendingTemplate (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) :=
  descendingProgramTemplate (tickCoordinateListTemplate tm kinds inputStride strideBound backward) (.inl 2)

theorem tickCoordinateListDescendingTemplate_embeds (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickCoordinateListDescendingTemplate tm kinds inputStride strideBound backward).Embeds :=
  descendingProgramTemplate_embeds _ _ (tickCoordinateListTemplate_embeds tm kinds inputStride strideBound backward)

theorem tickCoordinateListDescendingTemplate_run (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickCoordinateListDescendingTemplate tm kinds inputStride strideBound backward).Runs :=
  descendingProgramTemplate_run _ _ (tickCoordinateListTemplate_embeds tm kinds inputStride strideBound backward)
    (tickCoordinateListTemplate_run tm kinds inputStride strideBound backward)

theorem tickCoordinateListDescendingTemplate_ready (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) (wireBound layers capacity : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hsize : tickSizeBound tm ≤ strideBound)
    (hs : TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) (cs (.inl 2))
      (⟨none,cs,[]⟩ : CounterCfg _ ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3)))) :
    (tickCoordinateListDescendingTemplate tm kinds inputStride strideBound backward).ready cs := by
  let p := tickCoordinateListTemplate tm kinds inputStride strideBound backward
  change descendingTemplateReady p (.inl 2) (cs (.inl 2)) cs
  refine descendingTemplateReady_of_invariant p (.inl 2)
    (fun k (t : CounterCfg _ (p.Labels (Fin 3))) => TickDescendingBudgetInvariant tm inputStride strideBound wireBound layers capacity
      (kinds.length*(37*tickSizeBound tm+1)) k t) ?_ ?_ ?_ (cs (.inl 2)) ⟨none,cs,[]⟩ hs
  · intro k t ht
    apply tickCoordinateListTemplate_ready
    simpa [fixedGuardedEmitterReady] using ht.1.1
  · intro k t ht
    rw [tickCoordinateListTemplate_control_frame tm kinds inputStride strideBound backward _ 2 (by decide)]
    simp
  · intro k t ht
    exact tickCoordinateListDescendingBudget_next tm kinds inputStride strideBound backward
      wireBound layers capacity k t hsize ht

/-- The reusable continuation-bearing traversal inherits the actual loop's polynomial instruction clock. -/
theorem tickCoordinateListDescendingTemplate_clock (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      TickDescendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
        (kinds.length*(37*tickSizeBound tm+1)) (cs (.inl 2))
        (⟨none,cs,[]⟩ : CounterCfg _ ((tickCoordinateListTemplate tm kinds inputStride strideBound backward).Labels (Fin 3))) →
      (tickCoordinateListDescendingTemplate tm kinds inputStride strideBound backward).steps cs ≤ clock.eval n := by
  obtain ⟨clock,hclock⟩ := tickCoordinateListDescendingTraversal_polynomial tm kinds inputStride strideBound backward
    capacity budget layers hsize
  refine ⟨clock,?_⟩
  intro n cs hs
  let p := tickCoordinateListTemplate tm kinds inputStride strideBound backward
  let s : CounterCfg _ (p.Labels (Fin 3)) := ⟨none,cs,[]⟩
  have h := hclock n (cs (.inl 2)) s hs
  change descendingSteps (templateDescendingBody p (.inl 2)) (templateDescendingCost p (.inl 2)) (cs (.inl 2)) s ≤ _ at h
  rw [descendingTemplateSteps_eq] at h
  exact h

end ShiReversibleGenerator
