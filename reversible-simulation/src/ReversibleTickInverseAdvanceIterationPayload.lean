import ReversibleTickInverseAdvanceIterationCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickInverseIterationBytes (tm : Turing.FinTM2) (bound capacity : Nat) :
    Nat → Nat → Nat → List Bool
  | 0,_,_ => []
  | k+1,input,outputBase =>
    tickInverseIterationBytes tm bound capacity k (outputBase+bound)
      (outputBase+configurationWidth tm capacity*(bound+1)) ++
    tickForestSymbolicPayload tm (bound+1) bound true input capacity outputBase

/-- The finite inverse loop prepends the next slice's bytes before the current slice's bytes. -/
theorem tickInverseAdvanceIterationBytes_symbolic (tm : Turing.FinTM2) (bound k : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    descendingTemplateBytes (tickInverseAdvanceStepTemplate tm (bound+1) bound) (tickTraversalSpare tm 3) k cs=
      tickInverseIterationBytes tm bound (cs (.inl 1)) k (cs (.inl 0)) (cs (tickTraversalSpare tm 2)) := by
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h =>
    (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
    rw [descendingTemplateBytes,ih,tickInverseAdvanceStepTemplate_bytes,tickForestTemplate_symbolic_payload,
      tickInverseAdvanceStepTemplate_input,tickInverseAdvanceStepTemplate_output,
      tickInverseAdvanceStepTemplate_control_frame tm (bound+1) bound _ 1 (by decide) (by decide) (by decide)]
    simp only [Function.update_of_ne h23,
      Function.update_of_ne (by simp [tickTraversalSpare] :
        (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
      Function.update_of_ne (by simp [tickTraversalSpare] :
        (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 3),
      tickInverseIterationBytes]

theorem tickInverseAdvanceIterationTemplate_symbolic_payload (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInverseAdvanceIterationTemplate tm bound).bytes cs=
      tickInverseIterationBytes tm bound (cs (.inl 1)) (cs (tickTraversalSpare tm 3))
        (cs (.inl 0)) (cs (tickTraversalSpare tm 2)) :=
  tickInverseAdvanceIterationBytes_symbolic tm bound _ cs

/-- Exact agreement with the reverse of the established chronological padded iteration. -/
theorem tickInverseIterationBytes_agreement (tm : Turing.FinTM2) (bound capacity k input outputBase : Nat)
    (hc : 0 < capacity) :
    tickInverseIterationBytes tm bound capacity k input outputBase=
      ((paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound k
        (fun j => input+(bound+1)*j.val) outputBase).reverse.map (rawAssignmentPayload true)).flatten := by
  induction k generalizing input outputBase with
  | zero => rfl
  | succ k ih =>
    rw [tickInverseIterationBytes,paddedIterationCompile,List.reverse_append,List.map_append,List.flatten_append,ih]
    have hi : (fun j : Fin (configurationWidth tm capacity) =>
        outputBase+bound+(bound+1)*j.val)=(fun j => paddedForestResult outputBase bound j.val) := by
      funext j
      simp only [paddedForestResult]
      ring
    rw [hi,tickForestSymbolicPayload_agreement tm capacity input (bound+1) outputBase bound true hc]
    rfl

end ShiReversibleGenerator
