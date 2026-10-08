import ReversibleTickStackTraversalFinalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickStackListTemplate (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :=
  listProgramTemplate (stackOrder.map (fun k => tickStackTraversalTemplate tm k inputStride strideBound backward))

theorem tickStackListTemplate_embeds (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickStackListTemplate tm stackOrder inputStride strideBound backward).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
  exact tickStackTraversalTemplate_embeds tm k inputStride strideBound backward

theorem tickStackListTemplate_run (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) :
    (tickStackListTemplate tm stackOrder inputStride strideBound backward).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact tickStackTraversalTemplate_embeds tm k inputStride strideBound backward
  · intro p hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact tickStackTraversalTemplate_run tm k inputStride strideBound backward

/-- Every stack returns the same source/window and scratch invariants to the next stack. -/
theorem tickStackListTemplate_ready_and_budget (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hsize : tickSizeBound tm ≤ strideBound) :
    (tickStackListTemplate tm stackOrder inputStride strideBound backward).ready cs ∧
    CounterBudget ((tickStackListTemplate tm stackOrder inputStride strideBound backward).counters cs) (.inl 9) wireBound ∧
    TickWindowBudget tm inputStride strideBound wireBound
      ((tickStackListTemplate tm stackOrder inputStride strideBound backward).counters cs) ∧
    fixedGuardedEmitterReady (tickTraversalSupply tm)
      ((tickStackListTemplate tm stackOrder inputStride strideBound backward).counters cs) := by
  induction stackOrder generalizing cs with
  | nil => exact ⟨trivial,hb,hw,hr⟩
  | cons k stackOrder ih =>
    let after := (tickStackTraversalTemplate tm k inputStride strideBound backward).counters cs
    have hh := tickStackTraversalTemplate_ready tm k inputStride strideBound backward wireBound (cs (.inl 9))
      cs hr hb hw le_rfl hsize
    have hf := tickStackTraversalTemplate_final_bounds tm k inputStride strideBound backward wireBound (cs (.inl 9))
      cs hr hb hw le_rfl hsize
    have ht := ih after hf.2.2.1 hf.1 hf.2.1
    exact ⟨⟨hh,ht.1⟩,ht.2⟩

theorem tickStackListTemplate_control_frame (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (q : Fin 14) (h2 : q ≠ 2) (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickStackListTemplate tm stackOrder inputStride strideBound backward).counters cs (.inl q)=cs (.inl q) := by
  induction stackOrder generalizing cs with
  | nil => rfl
  | cons k stackOrder ih =>
    change (tickStackListTemplate tm stackOrder inputStride strideBound backward).counters
      ((tickStackTraversalTemplate tm k inputStride strideBound backward).counters cs) (.inl q)=_
    rw [ih,tickStackTraversalTemplate_control_frame tm k inputStride strideBound backward cs q h2 hq]

theorem tickStackListTemplate_spare_frame (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (j : Fin 8) (hj : j ≠ 0) :
    (tickStackListTemplate tm stackOrder inputStride strideBound backward).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) := by
  induction stackOrder generalizing cs with
  | nil => rfl
  | cons k stackOrder ih =>
    change (tickStackListTemplate tm stackOrder inputStride strideBound backward).counters
      ((tickStackTraversalTemplate tm k inputStride strideBound backward).counters cs) (tickTraversalSpare tm j)=_
    rw [ih,tickStackTraversalTemplate_spare_frame tm k inputStride strideBound backward cs j hj]

end ShiReversibleGenerator
