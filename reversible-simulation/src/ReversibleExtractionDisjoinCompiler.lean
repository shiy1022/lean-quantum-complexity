import ReversibleFormulaRaw

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

/-- Exact suffix size for the right-fold output selection, rather than a padded upper bound. -/
theorem disjoin_size_exact (ps : List (Formula ι)) :
    (disjoin ps).size=1+(ps.map (fun p => p.size+4)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [disjoin,List.foldr_cons,Formula.size_disj]
    change p.size+(disjoin ps).size+4=_
    rw [ih]
    simp only [List.map_cons,List.sum_cons]
    omega

/-- Explicit postorder compiler recurrence for dynamic output selection.
The suffix starts after the term's negation; its size determines all three closing nodes. -/
def disjoinRawCompile (inputs : ι → Nat) (base : Nat) : List (Formula ι) → List RawAssignment
  | [] => [.constant base false]
  | p::ps =>
    let suffixSize := (disjoin ps).size
    let suffixBase := base+p.size+1
    (p.rawCompile inputs base ++ [.neg (p.result base) (base+p.size)]) ++
      disjoinRawCompile inputs suffixBase ps ++
      [.neg (suffixBase+suffixSize-1) (suffixBase+suffixSize),
        .conj (base+p.size) (suffixBase+suffixSize) (suffixBase+suffixSize+1),
        .neg (suffixBase+suffixSize+1) (suffixBase+suffixSize+2)]

theorem disjoin_rawCompile_recurrence (ps : List (Formula ι)) (inputs : ι → Nat) (base : Nat) :
    (disjoin ps).rawCompile inputs base=disjoinRawCompile inputs base ps := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    simp only [disjoin,List.foldr_cons]
    change (p.disj (disjoin ps)).rawCompile inputs base=_
    simp [disjoinRawCompile,Formula.disj,Formula.rawCompile,Formula.result,Formula.size,
      ih,Nat.add_assoc,List.append_assoc]
    omega

/-- The explicit dynamic recurrence emits exactly the actual number of raw assignments. -/
theorem disjoinRawCompile_length (ps : List (Formula ι)) (inputs : ι → Nat) (base : Nat) :
    (disjoinRawCompile inputs base ps).length=1+(ps.map (fun p => p.size+4)).sum := by
  rw [←disjoin_rawCompile_recurrence,Formula.rawCompile_length,disjoin_size_exact]

end ShiReversibleFormula
