import ReversibleTickRetreatStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickRetreatStepTemplate_input (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickRetreatStepTemplate tm inputStride bound).counters cs (.inl 0)=
      cs (.inl 0)-configurationWidth tm (cs (.inl 1))*(bound+1) := by
  change (tickWindowRetreatTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (.inl 0)=_
  rw [tickWindowRetreatTemplate_counters]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 4),
    Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 2),Function.update_self]
  rw [tickForestTemplate_control_frame tm inputStride bound false cs 0 (by decide) (by decide),
    tickForestTemplate_control_frame tm inputStride bound false cs 1 (by decide) (by decide)]

theorem tickRetreatStepTemplate_output (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickRetreatStepTemplate tm inputStride bound).counters cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 2)-configurationWidth tm (cs (.inl 1))*(bound+1) := by
  change (tickWindowRetreatTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (tickTraversalSpare tm 2)=_
  rw [tickWindowRetreatTemplate_counters,
    Function.update_of_ne (fun h => (by decide : (2 : Fin 8) ≠ 4) (tickTraversalSpare_injective tm h)),Function.update_self,
    tickForestTemplate_spare_frame tm inputStride bound false cs 2 (by decide),
    tickForestTemplate_control_frame tm inputStride bound false cs 1 (by decide) (by decide)]

theorem tickRetreatStepTemplate_count (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickRetreatStepTemplate tm inputStride bound).counters cs (.inl 9)=
      cs (.inl 9)+tickForestLayerCount tm (cs (.inl 1)) := by
  change (tickWindowRetreatTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (.inl 9)=_
  rw [tickWindowRetreatTemplate_counters]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 4),
    Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 2),
    Function.update_of_ne (by simp : (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 0)]
  exact tickForestTemplate_count tm inputStride bound false cs

theorem tickRetreatStepTemplate_control_frame (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14) (h0 : q ≠ 0) (h2 : q ≠ 2)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickRetreatStepTemplate tm inputStride bound).counters cs (.inl q)=cs (.inl q) := by
  change (tickWindowRetreatTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (.inl q)=_
  rw [tickWindowRetreatTemplate_counters]
  rw [Function.update_of_ne (by simp [tickTraversalSpare]),Function.update_of_ne (by simp [tickTraversalSpare]),
    Function.update_of_ne (by simpa using h0)]
  exact tickForestTemplate_control_frame tm inputStride bound false cs q h2 hq

theorem tickRetreatStepTemplate_spare_frame (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) (h0 : j ≠ 0) (h2 : j ≠ 2) (h4 : j ≠ 4) :
    (tickRetreatStepTemplate tm inputStride bound).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) := by
  change (tickWindowRetreatTemplate tm bound).counters ((tickForestTemplate tm inputStride bound false).counters cs) (tickTraversalSpare tm j)=_
  rw [tickWindowRetreatTemplate_counters,
    Function.update_of_ne (fun h => h4 (tickTraversalSpare_injective tm h)),
    Function.update_of_ne (fun h => h2 (tickTraversalSpare_injective tm h)),Function.update_of_ne (by simp [tickTraversalSpare])]
  exact tickForestTemplate_spare_frame tm inputStride bound false cs j h0

theorem tickRetreatStepTemplate_ready_preserved (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((tickRetreatStepTemplate tm inputStride bound).counters cs) := by
  unfold fixedGuardedEmitterReady at hr ⊢
  have hf := tickRetreatStepTemplate_control_frame tm inputStride bound cs
  rcases hr with ⟨h3,h4,h5,h10,h11⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hf 3 (by decide) (by decide) (by decide)]; exact h3
  · rw [hf 4 (by decide) (by decide) (by decide)]; exact h4
  · rw [hf 5 (by decide) (by decide) (by decide)]; exact h5
  · rw [hf 10 (by decide) (by decide) (by decide)]; exact h10
  · rw [hf 11 (by decide) (by decide) (by decide)]; exact h11

end ShiReversibleGenerator
