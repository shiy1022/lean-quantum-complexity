import ReversibleTickInverseHistoryTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Exact inverse history bytes, including the initialized stride18 slice and every regular slice. -/
theorem tickInverseHistoryTemplate_payload (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hc : 0 < cs (.inl 1)) (ht : 0 < cs (tickTraversalSpare tm 7)) :
    (tickInverseHistoryTemplate tm bound).bytes cs=
      ((paddedIterationCompile (tickForest tm (cs (.inl 1))) (tickForest_length tm (cs (.inl 1))) bound
        (cs (tickTraversalSpare tm 7)) (fun j => cs (.inl 0)+18*j.val) (cs (tickTraversalSpare tm 2))).reverse.map
          (rawAssignmentPayload true)).flatten := by
  let initial := (tickHistoryCountTemplate tm).counters cs
  let after := (tickInverseAdvanceStepTemplate tm 18 bound).counters initial
  have hi : initial=Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1) := tickHistoryCountTemplate_counters tm cs
  have h23 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 3 := fun h =>
    (by decide : (2 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  have hi0 : initial (.inl 0)=cs (.inl 0) := by rw [hi]; simp [tickTraversalSpare]
  have hi1 : initial (.inl 1)=cs (.inl 1) := by rw [hi]; simp [tickTraversalSpare]
  have hi2 : initial (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2) := by rw [hi,Function.update_of_ne h23]
  have ha1 : after (.inl 1)=cs (.inl 1) :=
    (tickInverseAdvanceStepTemplate_control_frame tm 18 bound initial 1 (by decide) (by decide) (by decide)).trans hi1
  have ha3 : after (tickTraversalSpare tm 3)=cs (tickTraversalSpare tm 7)-1 := by
    dsimp only [after]
    rw [tickInverseAdvanceStepTemplate_spare_frame tm 18 bound _ 3 (by decide) (by decide),hi,Function.update_self]
  have ha0 : after (.inl 0)=cs (tickTraversalSpare tm 2)+bound := by
    dsimp only [after]
    rw [tickInverseAdvanceStepTemplate_input,hi2]
  have ha2 : after (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2)+
      configurationWidth tm (cs (.inl 1))*(bound+1) := by
    dsimp only [after]
    rw [tickInverseAdvanceStepTemplate_output,hi2,hi1]
  have hrest := (tickInverseAdvanceIterationTemplate_symbolic_payload tm bound after).trans
    (tickInverseIterationBytes_agreement tm bound (after (.inl 1)) (after (tickTraversalSpare tm 3))
      (after (.inl 0)) (after (tickTraversalSpare tm 2)) (by rw [ha1]; exact hc))
  rw [ha1,ha3,ha0,ha2] at hrest
  have hfirst := tickForestTemplate_payload tm 18 bound true initial (by rw [hi1]; exact hc)
  rw [hi0,hi1,hi2] at hfirst
  simp only [Bool.true_eq,if_true] at hfirst
  change (tickInverseAdvanceIterationTemplate tm bound).bytes after++
    (tickInverseAdvanceStepTemplate tm 18 bound).bytes initial++[]=_
  rw [List.append_nil,hrest,tickInverseAdvanceStepTemplate_bytes,hfirst]
  have hn : cs (tickTraversalSpare tm 7)-1+1=cs (tickTraversalSpare tm 7) := Nat.sub_add_cancel (Nat.succ_le_of_lt ht)
  conv_rhs => rw [←hn,paddedIterationCompile,List.reverse_append,List.map_append,List.flatten_append]
  have hnext : (fun j : Fin (configurationWidth tm (cs (.inl 1))) => cs (tickTraversalSpare tm 2)+bound+(bound+1)*j.val)=
      (fun j => paddedForestResult (cs (tickTraversalSpare tm 2)) bound j.val) := by
    funext j
    simp only [paddedForestResult]
    ring
  rw [hnext]

end ShiReversibleGenerator
