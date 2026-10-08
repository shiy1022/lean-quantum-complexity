import ReversibleTickForwardHistoryTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Exact forward history bytes include the initialized stride18 tick without a virtual input origin. -/
theorem tickForwardHistoryTemplate_payload (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    (hfirst : firstOutput=cs (tickTraversalSpare tm 6)+18*configurationWidth tm capacity) :
    (tickForwardHistoryTemplate tm bound).bytes cs=
      ((paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound
        (cs (tickTraversalSpare tm 3)+1) (fun j => cs (tickTraversalSpare tm 6)+17+18*j.val) firstOutput).map
          (rawAssignmentPayload false)).flatten := by
  let after := (tickRetreatIterationTemplate tm bound).counters cs
  let initial := (tickInitializedWindowTemplate tm).counters after
  have ha1 : after (.inl 1)=capacity := (tickRetreatIterationTemplate_capacity tm bound cs).trans hs.2.2.1
  have ha6 : after (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) :=
    tickRetreatIterationTemplate_spare_frame tm bound cs 6 (by decide) (by decide) (by decide) (by decide)
  have hi0 : initial (.inl 0)=cs (tickTraversalSpare tm 6)+17 := by
    dsimp only [initial]
    rw [tickInitializedWindowTemplate_input,ha6]
  have hi1 : initial (.inl 1)=capacity :=
    (tickInitializedWindowTemplate_control_frame tm after 1 (by decide)).trans ha1
  have hi2 : initial (tickTraversalSpare tm 2)=firstOutput := by
    dsimp only [initial]
    rw [tickInitializedWindowTemplate_output,ha6,ha1,←hfirst]
  have hrest := tickRetreatHistoryTemplate_payload tm bound wireBound capacity layers firstOutput cs hs hc hsize
  have hboundary := tickForestTemplate_payload tm 18 bound false initial (by rw [hi1]; exact hc)
  rw [hi0,hi1,hi2] at hboundary
  simp at hboundary
  change ((tickForestTemplate tm 18 bound false).bytes initial++(tickInitializedWindowTemplate tm).bytes after)++
    (tickRetreatIterationTemplate tm bound).bytes cs=_
  rw [tickInitializedWindowTemplate_bytes,List.append_nil,hboundary,hrest,paddedIterationCompile,
    List.map_append,List.flatten_append]
  have hnext : (fun j : Fin (configurationWidth tm capacity) => firstOutput+bound+(bound+1)*j.val)=
      (fun j => paddedForestResult firstOutput bound j.val) := by
    funext j
    simp only [paddedForestResult]
    ring
  rw [hnext]

end ShiReversibleGenerator
