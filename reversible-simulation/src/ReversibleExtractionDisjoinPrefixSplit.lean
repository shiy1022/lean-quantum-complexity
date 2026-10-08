import ReversibleExtractionDisjoinPasses

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

/-- Exact concatenation law for the original compiler's term-prefix pass. -/
theorem disjoinTermPrefix_append (inputs : ι → Nat) (base : Nat) (ps qs : List (Formula ι)) :
    disjoinTermPrefix inputs base (ps++qs)=
      disjoinTermPrefix inputs base ps ++
        disjoinTermPrefix inputs (base+(ps.map (fun p => p.size+1)).sum) qs := by
  induction ps generalizing base with
  | nil => simp [disjoinTermPrefix]
  | cons p ps ih =>
    simp [disjoinTermPrefix,ih,List.append_assoc,Nat.add_assoc]

/-- Descending runtime printing prepends each original final term block. -/
theorem disjoinTermPrefix_snoc (inputs : ι → Nat) (base : Nat) (ps : List (Formula ι)) (p : Formula ι) :
    disjoinTermPrefix inputs base (ps++[p])=
      disjoinTermPrefix inputs base ps ++
        (p.rawCompile inputs (disjoinFalseBase base ps) ++
          [.neg (p.result (disjoinFalseBase base ps)) (disjoinFalseBase base ps+p.size)]) := by
  rw [disjoinTermPrefix_append,←disjoinFalseBase_exact]
  simp [disjoinTermPrefix]

end ShiReversibleFormula
