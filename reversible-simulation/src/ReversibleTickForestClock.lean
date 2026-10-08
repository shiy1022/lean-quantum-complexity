import ReversibleTickHeaderClock
import ReversibleTickForestInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual complete tick-forest instruction graph runs in polynomial time from concrete budgets. -/
theorem tickForestTemplate_clock (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (capacity budget layers : Polynomial Nat) (hsize : tickSizeBound tm ≤ strideBound) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      cs (.inl 1)=capacity.eval n → fixedGuardedEmitterReady (tickTraversalSupply tm) cs →
      CounterBudget cs (.inl 9) (budget.eval n) → TickWindowBudget tm inputStride strideBound (budget.eval n) cs →
      0 < cs (.inl 1) → cs (.inl 9) ≤ layers.eval n →
      (tickForestTemplate tm inputStride strideBound backward).steps cs ≤ clock.eval n := by
  cases backward with
  | false =>
    let ks := (tickStackOrder tm).reverse
    let inc := (ks.map (fun k => (tickSymbolRowKinds tm k).length)).sum*(37*tickSizeBound tm+1)
    let nextLayers := layers+capacity*Polynomial.C inc
    obtain ⟨cellClock,hcells⟩ := tickStackListTemplate_clock tm ks inputStride strideBound false capacity budget layers hsize
    obtain ⟨headerClock,hheader⟩ := tickHeaderTemplate_clock tm inputStride strideBound false budget nextLayers
    refine ⟨cellClock+headerClock,?_⟩
    intro n cs hcap hr hb hw _ hl
    let after := (tickStackListTemplate tm ks inputStride strideBound false).counters cs
    have hs := tickStackListTemplate_ready_and_budget tm ks inputStride strideBound false (budget.eval n) cs hr hb hw hsize
    have hcount := tickStackListTemplate_layer_bound tm ks inputStride strideBound false (budget.eval n) cs hr hb hw hsize
    have hnext : after (.inl 9) ≤ nextLayers.eval n := by
      calc
        _ ≤ cs (.inl 9)+cs (.inl 1)*inc := hcount
        _ ≤ layers.eval n+capacity.eval n*inc := Nat.add_le_add hl (by rw [hcap])
        _ = _ := by simp only [nextLayers,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    have hh := hheader n after hs.2.2.2 hs.2.1 hnext
    have hc := hcells n cs hcap hr hb hw hl
    change (tickStackListTemplate tm ks inputStride strideBound false).steps cs+
      (tickHeaderTemplate tm inputStride strideBound false).steps after ≤ _
    simpa only [Polynomial.eval_add] using Nat.add_le_add hc hh
  | true =>
    let nextLayers := layers+Polynomial.C ((tickHeaderKinds tm).length*(37*tickSizeBound tm+1))
    obtain ⟨headerClock,hheader⟩ := tickHeaderTemplate_clock tm inputStride strideBound true budget layers
    obtain ⟨cellClock,hcells⟩ := tickStackListTemplate_clock tm (tickStackOrder tm) inputStride strideBound true capacity budget nextLayers hsize
    refine ⟨headerClock+cellClock,?_⟩
    intro n cs hcap hr hb hw hpos hl
    let after := (tickHeaderTemplate tm inputStride strideBound true).counters cs
    have hs := tickHeaderTemplate_final_bounds tm inputStride strideBound true (budget.eval n) cs hb hw hpos hsize
    have ha : after (.inl 1)=capacity.eval n := by
      dsimp only [after]
      rw [tickHeaderTemplate_control_frame tm inputStride strideBound true cs 1 (by decide) (by decide)]
      exact hcap
    have hnext : after (.inl 9) ≤ nextLayers.eval n := by
      simpa only [nextLayers,Polynomial.eval_add,Polynomial.eval_C] using
        hs.2.2.trans (Nat.add_le_add_right hl ((tickHeaderKinds tm).length*(37*tickSizeBound tm+1)))
    have hh := hheader n cs hr hb hl
    have hc := hcells n after ha (tickHeaderTemplate_ready_preserved tm inputStride strideBound true cs hr) hs.1 hs.2.1 hnext
    change (tickHeaderTemplate tm inputStride strideBound true).steps cs+
      (tickStackListTemplate tm (tickStackOrder tm) inputStride strideBound true).steps after ≤ _
    simpa only [Polynomial.eval_add] using Nat.add_le_add hh hc

end ShiReversibleGenerator
