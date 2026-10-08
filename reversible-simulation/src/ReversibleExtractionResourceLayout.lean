import ReversibleExtractionResourceMetadata
import ReversibleTickRuntimePolynomials

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Every final configuration result slot precedes the extraction forest, for the actual positive history budget. -/
theorem extractionFinalSource_lt_base (tm : Turing.FinTM2) (n time : Nat) (ht : 0 < time)
    (i : Fin (configurationWidth tm (n+time*machinePushBound tm+1))) :
    let width := configurationWidth tm (n+time*machinePushBound tm+1)
    let base := n+18*width+time*(width*(tickSizeBound tm+1))
    base-width*(tickSizeBound tm+1)+tickSizeBound tm+(tickSizeBound tm+1)*i.val < base := by
  let W := configurationWidth tm (n+time*machinePushBound tm+1)
  let S := tickSizeBound tm+1
  let base := n+18*W+time*(W*S)
  have hb : W*S ≤ base := by
    have hh := Nat.mul_le_mul_right (W*S) (by omega : 1 ≤ time)
    simp only [Nat.one_mul] at hh
    dsimp only [base]
    omega
  have hi : (i.val+1)*S ≤ W*S := Nat.mul_le_mul_right S (by have h := i.isLt; change i.val < W at h; omega)
  rw [Nat.add_mul,Nat.one_mul] at hi
  have he := Nat.sub_add_cancel hb
  have hs : S=tickSizeBound tm+1 := rfl
  change base-W*S+tickSizeBound tm+S*i.val < base
  rw [Nat.mul_comm S i.val]
  omega

/-- The original fixed-width extraction forest ends exactly at the physical output-copy region. -/
theorem extractionForestEnd_eq_output (tm : Turing.FinTM2) (n time : Nat) :
    let cap := n+time*machinePushBound tm+1
    n+18*configurationWidth tm cap+time*(configurationWidth tm cap*(tickSizeBound tm+1))+
      (2*cap+1)*(extractionBitBound tm cap+1)=n+paddedMachineWorkspace tm n time := by
  simp [paddedMachineWorkspace,Nat.add_assoc]
  exact Nat.mul_comm _ _

end ShiReversibleGenerator
