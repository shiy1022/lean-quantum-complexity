import ReversibleExtractionPaddedLeaf
import ReversibleExtractionForwardPassPayload
import ReversibleExtractionQuantumEncoding
import ReversibleExtractionPaddedPayload

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual padded forward leaf emits the established padded compiler, including its final CNOT. -/
theorem extractionPaddedLeafTemplate_forward_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride slotBound : Nat) (cs : ExtractionPaddedRegister → Nat)
    (hell : cs 2=0) (hcount : cs 9=cs 0+1)
    (hend : cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)).map (fun p => p.size+4)).sum)
    (hsource : cs 24=(extractionFormula tm e (cs 0) (cs 1)).result (cs 18))
    (htarget : cs 25=cs 18+slotBound) :
    (extractionPaddedLeafTemplate tm e stride false).bytes cs=
      (((extractionFormula tm e (cs 0) (cs 1)).paddedCompile
        (fun i => cs 11+stride*i.val) (cs 18) slotBound).map (rawAssignmentPayload false)).flatten := by
  let u := extractionPaddedRootCopyTemplate.counters cs
  let small := fun r => u (extractionTraversalToPaddedRegister r)
  have hu : ∀ q : ExtractionPaddedRegister,q ≠ 16 → u q=cs q := by
    intro q hq
    exact Function.update_of_ne hq _ _
  have hs0 : small 0=cs 0 := hu _ (by decide)
  have hs1 : small 1=cs 1 := hu _ (by decide)
  have hs2 : small 2=cs 2 := hu _ (by decide)
  have hs9 : small 9=cs 9 := hu _ (by decide)
  have hs11 : small 11=cs 11 := hu _ (by decide)
  have hs18 : small 18=cs 18 := hu _ (by decide)
  have hs20 : small 20=cs 20 := hu _ (by decide)
  have hp := extractionForwardPassTemplate_payload tm e stride small
    (hs2.trans hell) (by rw [hs9,hs0]; exact hcount)
    (by rw [hs20,hs18,hs0,hs1]; exact hend)
  have hp' : (extractionPaddedPassTemplate tm e stride false).bytes u=
      ((extractionRawNodes tm e (cs 0) (cs 1) (cs 11) stride (cs 18)).map (rawAssignmentPayload false)).flatten :=
    hp.trans (by rw [hs0,hs1,hs11,hs18,extractionRawNodes_natural])
  have hc := extractionPaddedRootCopyTemplate_payload cs false
  rw [hsource,htarget] at hc
  change (extractionPaddedPassTemplate tm e stride false).bytes u ++ extractionPaddedRootCopyTemplate.bytes cs=_
  rw [hp',hc,paddedFormula_forward_payload]
  rfl

end ShiReversibleGenerator
