import ReversibleTickRetreatIterationPayload
import ReversiblePaddedIterationLastSlice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The virtual boundary input and output place the next regular slice at its actual source addresses. -/
theorem tickRetreatIterationBytes_agreement (tm : Turing.FinTM2) (bound capacity firstInput firstOutput k : Nat)
    (hc : 0 < capacity)
    (hcompatible : firstInput+configurationWidth tm capacity*(bound+1)=firstOutput+bound) :
    tickRetreatIterationBytes tm bound capacity firstInput firstOutput k=
      ((paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound k
        (fun j => firstInput+configurationWidth tm capacity*(bound+1)+(bound+1)*j.val)
        (firstOutput+configurationWidth tm capacity*(bound+1))).map (rawAssignmentPayload false)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tickRetreatIterationBytes,paddedIterationCompile_succ_last,List.map_append,List.flatten_append,←ih]
    have hi : (fun j : Fin (configurationWidth tm capacity) =>
        firstInput+(k+1)*(configurationWidth tm capacity*(bound+1))+(bound+1)*j.val)=
        paddedIterationRead (tickForest tm capacity) (tickForest_length tm capacity) bound k
          (fun j => firstInput+configurationWidth tm capacity*(bound+1)+(bound+1)*j.val)
          (firstOutput+configurationWidth tm capacity*(bound+1)) := by
      funext j
      cases k with
      | zero => simp only [paddedIterationRead,Nat.zero_add,Nat.one_mul]
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
theorem tickRetreatIterationTemplate_payload (tm : Turing.FinTM2)
    (bound wireBound capacity layers firstInput firstOutput : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hs : TickRetreatIterationBudget tm bound wireBound capacity layers firstInput firstOutput
      (cs (tickTraversalSpare tm 3)) cs) (hc : 0 < capacity) (hsize : tickSizeBound tm ≤ bound)
    (hcompatible : firstInput+configurationWidth tm capacity*(bound+1)=firstOutput+bound) :
    (tickRetreatIterationTemplate tm bound).bytes cs=
      ((paddedIterationCompile (tickForest tm capacity) (tickForest_length tm capacity) bound (cs (tickTraversalSpare tm 3))
        (fun j => firstInput+configurationWidth tm capacity*(bound+1)+(bound+1)*j.val)
        (firstOutput+configurationWidth tm capacity*(bound+1))).map (rawAssignmentPayload false)).flatten :=
  (tickRetreatIterationTemplate_symbolic_payload tm bound wireBound capacity layers firstInput firstOutput cs hs hc hsize).trans
    (tickRetreatIterationBytes_agreement tm bound capacity firstInput firstOutput _ hc hcompatible)

end ShiReversibleGenerator
