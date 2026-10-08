import ReversibleStridedLeafFieldBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem stridedSharedFixedGuardedEmitter_fields_bound {tm : Turing.FinTM2}
    (supply tree : TickGuardFormula tm) (inputStride : Nat)
    (hsub : ∀ p ∈ tree.leaves, p ∈ supply.leaves) (backward : Bool)
    (cs : FixedLeafRegister supply → Nat) (bound : Nat)
    (hi : ∀ c ∈ (tree.eval (TickIndexGuard.eval (cs (.inl 1)) (cs (.inl 2)))).inputList,
      stridedTickCoordinateAddress tm (fixedLeafBindingRegisters supply) inputStride c cs ≤ bound)
    (hb : cs (.inl 12) + (tree.eval (TickIndexGuard.eval (cs (.inl 1)) (cs (.inl 2)))).size ≤ bound)
    (hz : cs (.inl 13) ≤ bound) :
    let final := (stridedSharedFixedGuardedEmitter supply tree inputStride backward).counters cs
    final (.inl 6) ≤ bound ∧ final (.inl 7) ≤ bound ∧ final (.inl 8) ≤ bound := by
  unfold stridedSharedFixedGuardedEmitter stridedGuardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  apply stridedFixedLeafEmitter_fields_bound
  · exact hsub _ (DecisionTree.eval_mem_leaves _ _)
  · intro i
    exact hi _ (List.getElem_mem _)
  · exact hb
  · exact hz

/-- A selected tick leaf reads only the current finite input window. -/
theorem stridedTickTraversalEmitter_fields_bound (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (wireBound : Nat)
    (hi : cs (.inl 2) < cs (.inl 1))
    (hin : cs (.inl 0) + inputStride * configurationWidth tm (cs (.inl 1)) ≤ wireBound)
    (hout : cs (.inl 12) + tickSizeBound tm ≤ wireBound)
    (hz : cs (.inl 13) ≤ wireBound) :
    let final := (stridedTickTraversalEmitter tm kind inputStride backward).counters cs
    final (.inl 6) ≤ wireBound ∧ final (.inl 7) ≤ wireBound ∧ final (.inl 8) ≤ wireBound := by
  apply stridedSharedFixedGuardedEmitter_fields_bound _ _ inputStride (tickTraversalSupply_contains tm kind)
  · intro c hc
    have ha := tickTreeForKind_selected_input_address tm (cs (.inl 1)) ⟨cs (.inl 2), hi⟩ kind c hc
    have hm := Nat.mul_le_mul_left inputStride (Nat.le_of_lt ha)
    exact le_trans (Nat.add_le_add_left hm (cs (.inl 0))) hin
  · exact le_trans (Nat.add_le_add_left
      (tickTreeForKind_selected_size tm (cs (.inl 1)) ⟨cs (.inl 2), hi⟩ kind) (cs (.inl 12))) hout
  · exact hz

end ShiReversibleGenerator
