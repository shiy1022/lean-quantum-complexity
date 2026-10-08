import ReversibleExtractionDisjoinPasses

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

/-- The last term's closing group is first in the right-fold closing suffix. -/
theorem disjoinClosingSuffix_snoc (ps : List (Formula ι)) (p : Formula ι) (base endpoint : Nat) :
    disjoinClosingSuffix base endpoint (ps++[p])=
      [RawAssignment.neg (endpoint-3*ps.length-3) (endpoint-3*ps.length-2),
        .conj (base+(ps.map (fun p => p.size+1)).sum+p.size)
          (endpoint-3*ps.length-2) (endpoint-3*ps.length-1),
        .neg (endpoint-3*ps.length-1) (endpoint-3*ps.length)] ++
      disjoinClosingSuffix base endpoint ps := by
  induction ps generalizing base endpoint with
  | nil => simp [disjoinClosingSuffix]
  | cons q qs ih =>
    have he : endpoint-3-3*qs.length=endpoint-3*(q::qs).length := by
      simp only [List.length_cons,Nat.mul_succ]
      omega
    rw [List.cons_append,disjoinClosingSuffix,ih]
    simp only [disjoinClosingSuffix,List.map_cons,List.sum_cons,he,List.append_assoc]
    all_goals simp only [Nat.add_assoc]

end ShiReversibleFormula
