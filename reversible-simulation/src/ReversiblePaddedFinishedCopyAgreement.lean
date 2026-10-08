import ReversibleOutputCopySemanticAgreement

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula

/-- The semantic finished circuit reads exactly the fixed-stride extraction roots. -/
theorem paddedFinishedCircuit_read_strided {n m : Nat}
    (ps : List (Formula (Fin n))) (hp : ps.length=m)
    (qs rs : List (Formula (Fin m))) (hq : qs.length=m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps,p.size ≤ ib) (ht : ∀ p ∈ qs,p.size ≤ tb) (hr : ∀ p ∈ rs,p.size ≤ rb) :
    (paddedFinishedCircuit ps hp qs rs hq ib tb rb t hi ht hr).read=
      stridedOutputRead (n+ps.length*(ib+1)+t*(m*(tb+1))) (rb+1)
        (n+paddedFinishedSize ps qs rs ib tb rb t) rs.length (Nat.succ_pos _) (by
          simp [paddedFinishedSize,hq,Nat.add_assoc]) := by
  funext i
  apply Fin.ext
  simp only [paddedFinishedCircuit,stridedOutputRead,paddedForestResult]
  have h : n+ps.length*(ib+1)+t*(m*(tb+1))+rb+(rb+1)*i.val+1=
      n+ps.length*(ib+1)+t*(m*(tb+1))+(i.val+1)*(rb+1) := by ring
  simp only [Nat.mul_comm i.val (rb+1)] at ⊢
  omega

/-- Exact quantum substitution of the finished circuit's copy block agrees with the finite generator. -/
theorem paddedFinishedCircuit_copyOut_strided {n m : Nat}
    (ps : List (Formula (Fin n))) (hp : ps.length=m)
    (qs rs : List (Formula (Fin m))) (hq : qs.length=m) (ib tb rb t : Nat)
    (hi : ∀ p ∈ ps,p.size ≤ ib) (ht : ∀ p ∈ qs,p.size ≤ tb) (hr : ∀ p ∈ rs,p.size ≤ rb) :
    ShiReversibleGateBridge.substitute
      ((ShiReversible.copyOut (paddedFinishedCircuit ps hp qs rs hq ib tb rb t hi ht hr).read).map
        ShiReversibleGateBridge.flatInstruction)=
    stridedOutputCopyLayers (n+paddedFinishedSize ps qs rs ib tb rb t+rs.length)
      (n+ps.length*(ib+1)+t*(m*(tb+1))) (rb+1)
      (n+paddedFinishedSize ps qs rs ib tb rb t) rs.length (Nat.succ_pos _)
      (by simp [paddedFinishedSize,hq,Nat.add_assoc]) (Nat.le_refl _) := by
  rw [paddedFinishedCircuit_read_strided]
  exact (stridedOutputCopyLayers_copyOut _ _ _ _ _ _).symm

end ShiReversibleGenerator
