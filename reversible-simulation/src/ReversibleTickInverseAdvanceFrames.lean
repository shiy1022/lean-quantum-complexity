import ReversibleTickInverseAdvanceCounters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickInverseAdvanceStepTemplate_control_frame (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14) (h0 : q ≠ 0) (h2 : q ≠ 2)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).counters cs (.inl q)=cs (.inl q) := by
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound true).counters cs) (.inl q)=_
  rw [tickWindowAdvanceTemplate_counters]
  rw [Function.update_of_ne (by simp [tickTraversalSpare]),Function.update_of_ne (by simpa using h0)]
  exact tickForestTemplate_control_frame tm inputStride bound true cs q h2 hq

theorem tickInverseAdvanceStepTemplate_spare_frame (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) (h0 : j ≠ 0) (h2 : j ≠ 2) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) := by
  have hj : tickTraversalSpare tm j ≠ tickTraversalSpare tm 2 := fun h => h2 (tickTraversalSpare_injective tm h)
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound true).counters cs) (tickTraversalSpare tm j)=_
  rw [tickWindowAdvanceTemplate_counters,Function.update_of_ne hj,Function.update_of_ne (by simp [tickTraversalSpare])]
  exact tickForestTemplate_spare_frame tm inputStride bound true cs j h0

theorem tickInverseAdvanceStepTemplate_ready_preserved (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((tickInverseAdvanceStepTemplate tm inputStride bound).counters cs) := by
  unfold fixedGuardedEmitterReady at hr ⊢
  have hf := tickInverseAdvanceStepTemplate_control_frame tm inputStride bound cs
  rcases hr with ⟨h3,h4,h5,h10,h11⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hf 3 (by decide) (by decide) (by decide)]; exact h3
  · rw [hf 4 (by decide) (by decide) (by decide)]; exact h4
  · rw [hf 5 (by decide) (by decide) (by decide)]; exact h5
  · rw [hf 10 (by decide) (by decide) (by decide)]; exact h10
  · rw [hf 11 (by decide) (by decide) (by decide)]; exact h11

end ShiReversibleGenerator
