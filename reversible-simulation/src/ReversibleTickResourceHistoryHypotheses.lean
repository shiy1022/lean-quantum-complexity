import ReversibleTickResourceCounterBounds
import ReversibleTickMetadataHandoffResult
import ReversibleTickForestLayerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Concrete prelude metadata supplies every runtime hypothesis of the prepared forward history emitter. -/
theorem tickResourceHandoff_history_hypotheses (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hpull : ∀ r,cs (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r)
    (houtside : ∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) (ht : 0 < time.eval n) :
    let cap := n+time.eval n*machinePushBound tm+1
    let firstOutput := n+18*configurationWidth tm cap
    let budget := (resourceCounterBudgetPolynomial tm time).eval n+tickSizeBound tm+17
    let layers := time.eval n*configurationWidth tm cap*(37*tickSizeBound tm+1)
    let final := (tickMetadataHandoffTemplate tm).counters cs
    fixedGuardedEmitterReady (tickTraversalSupply tm) final ∧ CounterBudget final (.inl 9) budget ∧
      final (.inl 1)=cap ∧ 0 < cap ∧ 0 < final (tickTraversalSpare tm 7) ∧
      final (tickTraversalSpare tm 1)=firstOutput+final (tickTraversalSpare tm 7)*(configurationWidth tm cap*(tickSizeBound tm+1)) ∧
      final (tickTraversalSpare tm 1)+tickSizeBound tm ≤ budget ∧
      final (.inl 9)+(final (tickTraversalSpare tm 7)-1)*tickForestLayerCount tm cap ≤ layers ∧
      final (tickTraversalSpare tm 6)+17+18*configurationWidth tm cap ≤ budget ∧
      final (tickTraversalSpare tm 6)+18*configurationWidth tm cap+
        configurationWidth tm cap*(tickSizeBound tm+1) ≤ budget ∧
      firstOutput=final (tickTraversalSpare tm 6)+18*configurationWidth tm cap := by
  dsimp only
  let cap := n+time.eval n*machinePushBound tm+1
  let final := (tickMetadataHandoffTemplate tm).counters cs
  obtain ⟨hr,hraw,htime,hcap,hend,h0,h9⟩ := tickResourcePrelude_handoff_result tm n (time.eval n) cs hpull
  have hb := tickResourceHandoff_uniform_bound tm time n cs hpull houtside
  have hc : 0 < cap := by dsimp only [cap]; omega
  have he := hb (tickTraversalSpare tm 1)
  rw [hend] at he
  refine ⟨hr,?_,hcap,hc,?_,?_,?_,?_,?_,?_,?_⟩
  · intro q _
    have h := hb q
    omega
  · rw [htime]; exact ht
  · rw [hend,htime]
  · have h := hb (tickTraversalSpare tm 1)
    omega
  · rw [h9,htime,Nat.zero_add]
    calc
      (time.eval n-1)*tickForestLayerCount tm cap ≤ time.eval n*tickForestLayerCount tm cap :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ time.eval n*(configurationWidth tm cap*(37*tickSizeBound tm+1)) :=
        Nat.mul_le_mul_left _ (tickForestLayerCount_bound tm cap hc)
      _ = time.eval n*configurationWidth tm cap*(37*tickSizeBound tm+1) := by ring
  · rw [hraw]
    omega
  · rw [hraw]
    have hw := Nat.mul_le_mul_right (configurationWidth tm cap*(tickSizeBound tm+1)) (Nat.succ_le_of_lt ht)
    simp only [Nat.one_mul] at hw
    change n+18*configurationWidth tm cap+time.eval n*(configurationWidth tm cap*(tickSizeBound tm+1)) ≤
      (resourceCounterBudgetPolynomial tm time).eval n at he
    dsimp only [cap] at he hw ⊢
    omega
  · rw [hraw]

end ShiReversibleGenerator
