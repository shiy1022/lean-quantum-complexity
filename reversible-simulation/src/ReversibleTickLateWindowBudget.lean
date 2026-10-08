import ReversibleTickLateWindowFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickWindowRetreatTemplate_static_budget (tm : Turing.FinTM2) (bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hb : CounterBudget cs (.inl 9) wireBound) :
    CounterBudget ((tickWindowRetreatTemplate tm bound).counters cs) (.inl 9) wireBound := by
  rw [tickWindowRetreatTemplate_counters]
  exact ((hb.update _ _ ((Nat.sub_le _ _).trans (hb _ (by simp)))).update _ _
    ((Nat.sub_le _ _).trans (hb _ (by simp [tickTraversalSpare])))).update _ _ (Nat.zero_le _)

theorem tickInputRetreatTemplate_static_budget (tm : Turing.FinTM2) (bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hb : CounterBudget cs (.inl 9) wireBound) :
    CounterBudget ((tickInputRetreatTemplate tm bound).counters cs) (.inl 9) wireBound := by
  rw [tickInputRetreatTemplate_counters]
  exact ((hb.update _ _ ((Nat.sub_le _ _).trans (hb _ (by simp)))).update _ _
    ((Nat.sub_le _ _).trans (hb _ (by simp [tickTraversalSpare])))).update _ _ (Nat.zero_le _)

theorem tickLateWindowTemplate_static_budget (tm : Turing.FinTM2) (bound wireBound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hb : CounterBudget cs (.inl 9) wireBound)
    (hend : cs (tickTraversalSpare tm 1)+bound ≤ wireBound) :
    CounterBudget ((tickLateWindowTemplate tm bound).counters cs) (.inl 9) wireBound := by
  let a := (counterAffineCopyProgramTemplate (tickTraversalSpare tm 1) (.inl 0) (.inl 5) bound 1 0).counters cs
  let b := (counterAffineCopyProgramTemplate (tickTraversalSpare tm 1) (tickTraversalSpare tm 2) (.inl 5) 0 1 0).counters a
  have ha : CounterBudget a (.inl 9) wireBound := by
    change CounterBudget (Function.update cs (.inl 0) (1*cs (tickTraversalSpare tm 1)+bound-0)) (.inl 9) wireBound
    simp only [Nat.one_mul,Nat.sub_zero]
    exact hb.update _ _ hend
  have hb' : CounterBudget b (.inl 9) wireBound := by
    change CounterBudget (Function.update a (tickTraversalSpare tm 2) (1*a (tickTraversalSpare tm 1)+0-0)) (.inl 9) wireBound
    simp only [Nat.one_mul,Nat.add_zero,Nat.sub_zero]
    exact ha.update _ _ (ha _ (by simp [tickTraversalSpare]))
  change CounterBudget ((tickInputRetreatTemplate tm bound).counters ((tickWindowRetreatTemplate tm bound).counters b)) (.inl 9) wireBound
  exact tickInputRetreatTemplate_static_budget tm bound wireBound _
    (tickWindowRetreatTemplate_static_budget tm bound wireBound b hb')

theorem tickLateWindowTemplate_ready_preserved (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((tickLateWindowTemplate tm bound).counters cs) := by
  unfold fixedGuardedEmitterReady at hr ⊢
  have hf := tickLateWindowTemplate_control_frame tm bound cs
  rcases hr with ⟨h3,h4,h5,h10,h11⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hf 3 (by decide)]; exact h3
  · rw [hf 4 (by decide)]; exact h4
  · rw [hf 5 (by decide)]; exact h5
  · rw [hf 10 (by decide)]; exact h10
  · rw [hf 11 (by decide)]; exact h11

end ShiReversibleGenerator
