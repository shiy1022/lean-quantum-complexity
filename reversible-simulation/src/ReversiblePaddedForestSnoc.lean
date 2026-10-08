import ReversiblePaddedForest

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

/-- The final formula occupies the next fixed-width slot in the original padded forest compiler. -/
theorem paddedForestCompile_snoc (inputs : ι → Nat) (base bound : Nat)
    (ps : List (Formula ι)) (p : Formula ι) :
    paddedForestCompile inputs base bound (ps++[p])=paddedForestCompile inputs base bound ps ++
      p.paddedCompile inputs (base+ps.length*(bound+1)) bound := by
  induction ps generalizing base with
  | nil => simp [paddedForestCompile]
  | cons q qs ih =>
    simp only [List.cons_append,paddedForestCompile,ih,List.length_cons,Nat.succ_mul]
    simp only [Nat.add_assoc,List.append_assoc]
    congr 2
    congr 1
    omega

end ShiReversibleFormula
