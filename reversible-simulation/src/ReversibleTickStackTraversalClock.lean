import ReversibleTickSymbolRowLoopFinalBounds
import ReversibleTickAscendingLoopFinalBounds
import ReversibleCounterBudgetCleanupClock
import ReversibleTickStackTraversalPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Setup, traversal, and cleanup together have an actual polynomial instruction clock. -/
theorem tickStackTraversalTemplate_clock (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (capacity budget layers : Polynomial Nat)
    (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      cs (.inl 1)=capacity.eval n → fixedGuardedEmitterReady (tickTraversalSupply tm) cs →
      CounterBudget cs (.inl 9) (budget.eval n) → TickWindowBudget tm inputStride strideBound (budget.eval n) cs →
      cs (.inl 9) ≤ layers.eval n →
      (tickStackTraversalTemplate tm stack inputStride strideBound backward).steps cs ≤ clock.eval n := by
  cases backward with
  | false =>
    obtain ⟨clock,hclock⟩ := tickSymbolRowDescendingTemplate_clock tm stack inputStride strideBound false capacity budget layers hsize
    refine ⟨Polynomial.C 13*budget+Polynomial.C 5+clock,?_⟩
    intro n cs hcap hr hb hw hl
    let after := (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs
    let loop := descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound false) (.inl 2)
    let done := loop.counters after
    have hs := tickDescendingStackSetup_invariant tm inputStride strideBound (budget.eval n) (layers.eval n)
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) cs
      (L := (tickSymbolRowTemplate tm stack inputStride strideBound false).Labels (Fin 3)) hr hb hw hl
    have ha : after (.inl 2)=capacity.eval n := by simp [after,counterCopyProgramTemplate,hcap]
    have hs' : TickDescendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (after (.inl 2))
      (⟨none,after,[]⟩ : CounterCfg _ ((tickSymbolRowTemplate tm stack inputStride strideBound false).Labels (Fin 3))) := by
      rw [ha]
      simpa only [hcap] using hs
    have hc := hclock n after hs'
    have hf := tickSymbolRowDescendingTemplate_final_bounds tm stack inputStride strideBound false
      (budget.eval n) (layers.eval n) (capacity.eval n) after hsize hs'
    have hclear := cleanupSteps_counterBudget_bound [.inl 2,tickTraversalSpare tm 0] (.inl 9) done
      (budget.eval n) hf.1 (by simp [tickTraversalSpare])
    have h2 := hb (.inl 2) (by simp)
    have h1 := hb (.inl 1) (by simp)
    change (2*cs (.inl 2)+1+(7*cs (.inl 1)+2))+
      (loop.steps after+cleanupSteps [.inl 2,tickTraversalSpare tm 0] done) ≤ _
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    simp only [List.length_cons,List.length_nil] at hclear
    change loop.steps after ≤ clock.eval n at hc
    omega
  | true =>
    obtain ⟨clock,hclock⟩ := tickSymbolRowAscendingTemplate_clock tm stack inputStride strideBound true capacity budget layers hsize
    refine ⟨Polynomial.C 15*budget+Polynomial.C 6+clock,?_⟩
    intro n cs hcap hr hb hw hl
    let cleared := (cleanupProgramTemplate [.inl 2]).counters cs
    let after := (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters cleared
    let loop := tickSymbolRowAscendingTemplate tm stack inputStride strideBound true
    let done := loop.counters after
    have hs := tickAscendingStackSetup_invariant tm inputStride strideBound (budget.eval n) (layers.eval n)
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) cs
      (L := (tickSymbolRowAscendingBody tm stack inputStride strideBound true).Labels (Fin 3)) hr hb hw hl
    have ha : after (tickTraversalSpare tm 0)=capacity.eval n := by
      simp [after,cleared,counterCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters,hcap]
    have hs' : TickAscendingBudgetInvariant tm inputStride strideBound (budget.eval n) (layers.eval n) (capacity.eval n)
      ((tickSymbolRowKinds tm stack).length*(37*tickSizeBound tm+1)) (after (tickTraversalSpare tm 0))
      (⟨none,after,[]⟩ : CounterCfg _ ((tickSymbolRowAscendingBody tm stack inputStride strideBound true).Labels (Fin 3))) := by
      rw [ha]
      simpa only [hcap] using hs
    have hc := hclock n after hs'
    have hf := tickSymbolRowAscendingTemplate_final_bounds tm stack inputStride strideBound true
      (budget.eval n) (layers.eval n) (capacity.eval n) after hsize hs'
    have hclear := cleanupSteps_counterBudget_bound [.inl 2,tickTraversalSpare tm 0] (.inl 9) done
      (budget.eval n) hf.1 (by simp [tickTraversalSpare])
    have h2 := hb (.inl 2) (by simp)
    have h1 := hb (.inl 1) (by simp)
    have h0 := hb (tickTraversalSpare tm 0) (by simp [tickTraversalSpare])
    have hcopy : (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).steps cleared =
      2*cs (tickTraversalSpare tm 0)+1+(7*cs (.inl 1)+2) := by
      simp [counterCopyProgramTemplate,cleared,cleanupProgramTemplate,cleanupCounters,tickTraversalSpare]
    change cleanupSteps [.inl 2] cs+
      ((counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).steps cleared+
        (loop.steps after+cleanupSteps [.inl 2,tickTraversalSpare tm 0] done)) ≤ _
    rw [hcopy]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    have hstart : cleanupSteps [.inl 2] cs=2*cs (.inl 2)+1 := by simp [cleanupSteps]
    rw [hstart]
    simp only [List.length_cons,List.length_nil] at hclear
    change loop.steps after ≤ clock.eval n at hc
    omega

end ShiReversibleGenerator
