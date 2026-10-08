import ReversibleTickStackListTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The fixed finite stack composition has an actual polynomial instruction clock. -/
theorem tickStackListTemplate_clock (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      cs (.inl 1)=capacity.eval n → fixedGuardedEmitterReady (tickTraversalSupply tm) cs →
      CounterBudget cs (.inl 9) (budget.eval n) → TickWindowBudget tm inputStride strideBound (budget.eval n) cs →
      cs (.inl 9) ≤ layers.eval n →
      (tickStackListTemplate tm stackOrder inputStride strideBound backward).steps cs ≤ clock.eval n := by
  induction stackOrder generalizing layers with
  | nil =>
    refine ⟨0,?_⟩
    intro n cs _ _ _ _ _
    simp [tickStackListTemplate,listProgramTemplate,identityProgramTemplate]
  | cons k stackOrder ih =>
    let increment := (tickSymbolRowKinds tm k).length*(37*tickSizeBound tm+1)
    let nextLayers := layers+capacity*Polynomial.C increment
    obtain ⟨headClock,hhead⟩ := tickStackTraversalTemplate_clock tm k inputStride strideBound backward capacity budget layers hsize
    obtain ⟨tailClock,htail⟩ := ih nextLayers
    refine ⟨headClock+tailClock,?_⟩
    intro n cs hcap hr hb hw hl
    let after := (tickStackTraversalTemplate tm k inputStride strideBound backward).counters cs
    have hh := hhead n cs hcap hr hb hw hl
    have hf := tickStackTraversalTemplate_final_bounds tm k inputStride strideBound backward
      (budget.eval n) (layers.eval n) cs hr hb hw hl hsize
    have ha : after (.inl 1)=capacity.eval n := by
      dsimp only [after]
      rw [tickStackTraversalTemplate_control_frame tm k inputStride strideBound backward cs 1 (by decide) (by decide)]
      exact hcap
    have hlay : after (.inl 9) ≤ nextLayers.eval n := by
      simpa only [nextLayers,increment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,hcap] using hf.2.2.2
    have ht := htail n after ha hf.2.2.1 hf.1 hf.2.1 hlay
    change (tickStackTraversalTemplate tm k inputStride strideBound backward).steps cs+
      (tickStackListTemplate tm stackOrder inputStride strideBound backward).steps after ≤ _
    simpa only [Polynomial.eval_add] using Nat.add_le_add hh ht

end ShiReversibleGenerator
