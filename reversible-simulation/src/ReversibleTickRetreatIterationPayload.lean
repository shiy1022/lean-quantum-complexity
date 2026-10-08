import ReversibleTickRetreatIterationFinalBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickRetreatIterationBytes (tm : Turing.FinTM2) (bound capacity firstInput firstOutput : Nat) : Nat → List Bool
  | 0 => []
  | k+1 => tickRetreatIterationBytes tm bound capacity firstInput firstOutput k ++
    tickForestSymbolicPayload tm (bound+1) bound false
      (firstInput+(k+1)*(configurationWidth tm capacity*(bound+1))) capacity
      (firstOutput+(k+1)*(configurationWidth tm capacity*(bound+1)))

/-- Late-to-early execution prepends the forward slice blocks in chronological order. -/
theorem tickRetreatIterationBytes_symbolic (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstInput firstOutput k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput k cs)
    (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    descendingTemplateBytes (tickRetreatStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3) k cs=
      tickRetreatIterationBytes tm bound capacity firstInput firstOutput k := by
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h =>
    (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
    have hn := tickRetreatIterationBudget_next tm bound wireBound capacity layers firstInput firstOutput k cs hs hc hsize
    rw [descendingTemplateBytes,ih _ hn,tickRetreatStepTemplate_bytes,tickForestTemplate_symbolic_payload]
    simp only [Function.update_of_ne h23,
      Function.update_of_ne (by simp [tickTraversalSpare] :
        (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
      Function.update_of_ne (by simp [tickTraversalSpare] :
        (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3)]
    rw [hs.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1]
    rfl

theorem tickRetreatIterationTemplate_symbolic_payload (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstInput firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound) :
    (tickRetreatIterationTemplate tm bound).bytes cs=
      tickRetreatIterationBytes tm bound capacity firstInput firstOutput (cs (tickTraversalSpare tm 3)) :=
  tickRetreatIterationBytes_symbolic tm bound wireBound capacity layers firstInput firstOutput _ cs hs hc hsize

end ShiReversibleGenerator
