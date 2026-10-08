import ReversibleTickHeaderInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Concrete initial invariants make the complete finite forest program executable. -/
theorem tickForestTemplate_ready_and_budget (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (wireBound : Nat) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hc : 0 < cs (.inl 1)) (hsize : tickSizeBound tm ≤ strideBound) :
    (tickForestTemplate tm inputStride strideBound backward).ready cs ∧
    CounterBudget ((tickForestTemplate tm inputStride strideBound backward).counters cs) (.inl 9) wireBound ∧
    TickWindowBudget tm inputStride strideBound wireBound ((tickForestTemplate tm inputStride strideBound backward).counters cs) ∧
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((tickForestTemplate tm inputStride strideBound backward).counters cs) := by
  cases backward with
  | false =>
    let ks := (tickStackOrder tm).reverse
    let after := (tickStackListTemplate tm ks inputStride strideBound false).counters cs
    have hs := tickStackListTemplate_ready_and_budget tm ks inputStride strideBound false wireBound cs hr hb hw hsize
    have ha : 0 < after (.inl 1) := by
      dsimp only [after]
      rw [tickStackListTemplate_control_frame tm ks inputStride strideBound false cs 1 (by decide) (by decide)]
      exact hc
    have hh := tickHeaderTemplate_final_bounds tm inputStride strideBound false wireBound after hs.2.1 hs.2.2.1 ha hsize
    exact ⟨⟨hs.1,tickHeaderTemplate_ready tm inputStride strideBound false after hs.2.2.2⟩,
      hh.1,hh.2.1,tickHeaderTemplate_ready_preserved tm inputStride strideBound false after hs.2.2.2⟩
  | true =>
    let after := (tickHeaderTemplate tm inputStride strideBound true).counters cs
    have hh := tickHeaderTemplate_final_bounds tm inputStride strideBound true wireBound cs hb hw hc hsize
    have hs := tickStackListTemplate_ready_and_budget tm (tickStackOrder tm) inputStride strideBound true wireBound after
      (tickHeaderTemplate_ready_preserved tm inputStride strideBound true cs hr) hh.1 hh.2.1 hsize
    exact ⟨⟨tickHeaderTemplate_ready tm inputStride strideBound true cs hr,hs.1⟩,hs.2⟩

theorem tickForestTemplate_control_frame (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14) (h2 : q ≠ 2)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickForestTemplate tm inputStride strideBound backward).counters cs (.inl q)=cs (.inl q) := by
  cases backward with
  | false =>
    change (tickHeaderTemplate tm inputStride strideBound false).counters
      ((tickStackListTemplate tm (tickStackOrder tm).reverse inputStride strideBound false).counters cs) (.inl q)=_
    rw [tickHeaderTemplate_control_frame tm inputStride strideBound false _ q h2 hq,
      tickStackListTemplate_control_frame tm _ inputStride strideBound false cs q h2 hq]
  | true =>
    change (tickStackListTemplate tm (tickStackOrder tm) inputStride strideBound true).counters
      ((tickHeaderTemplate tm inputStride strideBound true).counters cs) (.inl q)=_
    rw [tickStackListTemplate_control_frame tm _ inputStride strideBound true _ q h2 hq,
      tickHeaderTemplate_control_frame tm inputStride strideBound true cs q h2 hq]

theorem tickForestTemplate_spare_frame (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) (hj : j ≠ 0) :
    (tickForestTemplate tm inputStride strideBound backward).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) := by
  cases backward with
  | false =>
    change (tickHeaderTemplate tm inputStride strideBound false).counters
      ((tickStackListTemplate tm (tickStackOrder tm).reverse inputStride strideBound false).counters cs) (tickTraversalSpare tm j)=_
    rw [tickHeaderTemplate_spare_frame,tickStackListTemplate_spare_frame tm _ inputStride strideBound false cs j hj]
  | true =>
    change (tickStackListTemplate tm (tickStackOrder tm) inputStride strideBound true).counters
      ((tickHeaderTemplate tm inputStride strideBound true).counters cs) (tickTraversalSpare tm j)=_
    rw [tickStackListTemplate_spare_frame tm _ inputStride strideBound true _ j hj,tickHeaderTemplate_spare_frame]

end ShiReversibleGenerator
