import ReversibleExtractionPaddedLeaf
import ReversibleExtractionInversePassPayload
import ReversibleExtractionQuantumEncoding
import ReversibleExtractionPaddedPayload

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual padded inverse leaf prepends the padded-root CNOT to the original reversed formula payload. -/
theorem extractionPaddedLeafTemplate_inverse_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride slotBound : Nat) (cs : ExtractionPaddedRegister → Nat)
    (hell : cs 2=0) (hcount : cs 22=cs 0+1)
    (hsource : cs 24=(extractionFormula tm e (cs 0) (cs 1)).result (cs 18))
    (htarget : cs 25=cs 18+slotBound) :
    (extractionPaddedLeafTemplate tm e stride true).bytes cs=
      ((((extractionFormula tm e (cs 0) (cs 1)).paddedCompile
        (fun i => cs 11+stride*i.val) (cs 18) slotBound).reverse).map (rawAssignmentPayload true)).flatten := by
  let small := fun r => cs (extractionTraversalToPaddedRegister r)
  let u := (extractionPaddedPassTemplate tm e stride true).counters cs
  have hs0 : small 0=cs 0 := rfl
  have hs1 : small 1=cs 1 := rfl
  have hs2 : small 2=cs 2 := rfl
  have hs11 : small 11=cs 11 := rfl
  have hs18 : small 18=cs 18 := rfl
  have hs22 : small 22=cs 22 := rfl
  have hp := extractionInversePassTemplate_payload tm e stride small
    (hs2.trans hell) (by rw [hs22,hs0]; exact hcount)
  have hp' : (extractionPaddedPassTemplate tm e stride true).bytes cs=
      ((extractionRawNodes tm e (cs 0) (cs 1) (cs 11) stride (cs 18)).reverse.map (rawAssignmentPayload true)).flatten :=
    hp.trans (by rw [hs0,hs1,hs11,hs18,extractionRawNodes_natural])
  have hu24 : u 24=cs 24 := extractionPaddedPassTemplate_roots tm e stride true cs 24 (by decide)
  have hu25 : u 25=cs 25 := extractionPaddedPassTemplate_roots tm e stride true cs 25 (by decide)
  have hc := extractionPaddedRootCopyTemplate_payload u true
  rw [hu24,hu25,hsource,htarget] at hc
  change extractionPaddedRootCopyTemplate.bytes u ++ (extractionPaddedPassTemplate tm e stride true).bytes cs=_
  rw [hc,hp',paddedFormula_inverse_payload]
  rfl

end ShiReversibleGenerator
