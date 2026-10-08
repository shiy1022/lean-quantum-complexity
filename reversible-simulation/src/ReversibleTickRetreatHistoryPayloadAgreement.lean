import ReversibleTickRetreatHistoryPayload
import ReversiblePaddedIterationLastSlice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Chronological forward bytes need only the actual output boundary; no virtual natural input origin is assumed. -/
theorem tickRetreatHistoryBytes_agreement (tm : Turing.FinTM2) (bound capacity firstOutput k : Nat)
    (hc : 0 < capacity) :
    tickRetreatHistoryBytes tm bound capacity firstOutput k=
      ((paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound k
        (fun j => firstOutput+bound+(bound+1)*j.val)
        (firstOutput+configurationWidth tm capacity*(bound+1))).map (rawAssignmentPayload false)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tickRetreatHistoryBytes,paddedIterationCompile_succ_last,List.map_append,List.flatten_append,←ih]
    have hi : (fun j : Fin (configurationWidth tm capacity) =>
        firstOutput+k*(configurationWidth tm capacity*(bound+1))+bound+(bound+1)*j.val)=
        paddedIterationRead (tickForest tm capacity) (tickForest_length tm capacity) bound k
          (fun j => firstOutput+bound+(bound+1)*j.val)
          (firstOutput+configurationWidth tm capacity*(bound+1)) := by
      funext j
      cases k with
      | zero => simp only [paddedIterationRead,Nat.zero_mul,Nat.add_zero]
      | succ k =>
        rw [paddedIterationRead_succ,Nat.mul_comm j.val (bound+1)]
        simp only [Nat.add_mul,Nat.one_mul]
        omega
    have hb : firstOutput+(k+1)*(configurationWidth tm capacity*(bound+1))=
        firstOutput+configurationWidth tm capacity*(bound+1)+k*(configurationWidth tm capacity*(bound+1)) := by ring
    rw [←hi,←hb]
    congr 1
    exact tickForestSymbolicPayload_agreement tm capacity _ (bound+1) _ bound false hc

/-- Exact established chronological forward raw-assignment bytes from the actual finite loop. -/
theorem tickRetreatHistoryTemplate_payload (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatHistoryBudget tm bound wireBound capacity layers firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    :
    (tickRetreatIterationTemplate tm bound).bytes cs=
      ((paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound (cs (tickTraversalSpare tm 3))
        (fun j => firstOutput+bound+(bound+1)*j.val)
        (firstOutput+configurationWidth tm capacity*(bound+1))).map (rawAssignmentPayload false)).flatten :=
  (tickRetreatHistoryTemplate_symbolic_payload tm bound wireBound capacity layers firstOutput cs hs hc hsize).trans
    (tickRetreatHistoryBytes_agreement tm bound capacity firstOutput _ hc)

end ShiReversibleGenerator
