import ReversibleTickRetreatHistoryFinalBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickRetreatHistoryBytes (tm : Turing.FinTM2) (bound capacity firstOutput : Nat) : Nat → List Bool
  | 0 => []
  | k+1 => tickRetreatHistoryBytes tm bound capacity firstOutput k ++
    tickForestSymbolicPayload tm (bound+1) bound false
      (firstOutput+k*(configurationWidth tm capacity*(bound+1))+bound) capacity
      (firstOutput+(k+1)*(configurationWidth tm capacity*(bound+1)))

/-- Late-to-early execution prepends the forward slice blocks in chronological order. -/
theorem tickRetreatHistoryBytes_symbolic (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput k cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    descendingTemplateBytes (tickRetreatStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3) k cs=
      tickRetreatHistoryBytes tm bound capacity firstOutput k := by
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h =>
    (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
    have hn := tickRetreatHistoryBudget_next tm bound wireBound capacity layers firstOutput k cs hs hc hsize
    rw [descendingTemplateBytes,ih _ hn,tickRetreatStepTemplate_bytes,tickForestTemplate_symbolic_payload]
    simp only [Function.update_of_ne h23,
      Function.update_of_ne (by simp [tickTraversalSpare] :
        (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
      Function.update_of_ne (by simp [tickTraversalSpare] :
        (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3)]
    rw [hs.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1]
    have hi : (firstOutput+(k+1)*(configurationWidth tm capacity*(bound+1))+bound)-
        configurationWidth tm capacity*(bound+1)=firstOutput+k*(configurationWidth tm capacity*(bound+1))+bound := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    rw [hi]
    rfl

theorem tickRetreatHistoryTemplate_symbolic_payload (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    (tickRetreatIterationTemplate tm bound).bytes cs=
      tickRetreatHistoryBytes tm bound capacity firstOutput (cs (tickTraversalSpare tm 3)) :=
  tickRetreatHistoryBytes_symbolic tm bound wireBound capacity layers firstOutput _ cs hs hc hsize

end ShiReversibleGenerator
