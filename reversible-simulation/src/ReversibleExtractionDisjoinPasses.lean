import ReversibleExtractionDisjoinCompiler

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι : Type}

/-- Forward term prefixes: each term followed by its negation. -/
def disjoinTermPrefix (inputs : ι → Nat) (base : Nat) : List (Formula ι) → List RawAssignment
  | [] => []
  | p::ps => p.rawCompile inputs base ++ [.neg (p.result base) (base+p.size)] ++
      disjoinTermPrefix inputs (base+p.size+1) ps

/-- Position of the right fold's final false constant. -/
def disjoinFalseBase (base : Nat) : List (Formula ι) → Nat
  | [] => base
  | p::ps => disjoinFalseBase (base+p.size+1) ps

/-- Closing nodes can be emitted by a finite pass whose endpoint retreats by three per term. -/
def disjoinClosingSuffix (base endpoint : Nat) : List (Formula ι) → List RawAssignment
  | [] => []
  | p::ps => disjoinClosingSuffix (base+p.size+1) (endpoint-3) ps ++
      [.neg (endpoint-3) (endpoint-2),
        .conj (base+p.size) (endpoint-2) (endpoint-1),.neg (endpoint-1) endpoint]

theorem disjoinFalseBase_exact (ps : List (Formula ι)) (base : Nat) :
    disjoinFalseBase base ps=base+(ps.map (fun p => p.size+1)).sum := by
  induction ps generalizing base with
  | nil => simp [disjoinFalseBase]
  | cons p ps ih => simp [disjoinFalseBase,ih,Nat.add_assoc]

/-- Exact two-pass decomposition of the original raw compiler; no padded or alternative formula is introduced. -/
theorem disjoin_rawCompile_passes (ps : List (Formula ι)) (inputs : ι → Nat) (base : Nat) :
    (disjoin ps).rawCompile inputs base=
      disjoinTermPrefix inputs base ps ++ [.constant (disjoinFalseBase base ps) false] ++
        disjoinClosingSuffix base (base+(ps.map (fun p => p.size+4)).sum) ps := by
  induction ps generalizing base with
  | nil => simp [disjoin,Formula.rawCompile,disjoinTermPrefix,disjoinFalseBase,disjoinClosingSuffix]
  | cons p ps ih =>
    have he0 : base+(p.size+4+(ps.map (fun p => p.size+4)).sum)-3=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum := by omega
    have he1 : base+(p.size+4+(ps.map (fun p => p.size+4)).sum)-2=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum+1 := by omega
    have he2 : base+(p.size+4+(ps.map (fun p => p.size+4)).sum)-1=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum+2 := by omega
    have he3 : base+(p.size+4+(ps.map (fun p => p.size+4)).sum)=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum+3 := by omega
    have hroot : base+p.size+1+(disjoin ps).size-1=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum := by
      rw [disjoin_size_exact]
      omega
    rw [disjoin_size_exact] at hroot
    have ht1 : base+p.size+1+(1+(ps.map (fun p => p.size+4)).sum)=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum+1 := by omega
    have ht2 : base+p.size+1+(1+(ps.map (fun p => p.size+4)).sum)+1=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum+2 := by omega
    have ht3 : base+p.size+1+(1+(ps.map (fun p => p.size+4)).sum)+2=
        base+p.size+1+(ps.map (fun p => p.size+4)).sum+3 := by omega
    simp only [Nat.add_assoc] at he0 he1 he2 he3 hroot ht1 ht2 ht3
    rw [disjoin_rawCompile_recurrence]
    simp only [disjoinRawCompile]
    rw [←disjoin_rawCompile_recurrence,ih]
    simp only [disjoinTermPrefix,disjoinFalseBase,disjoinClosingSuffix,
      List.map_cons,List.sum_cons,disjoin_size_exact,List.append_assoc,Nat.add_assoc]
    simp only [he0,he1,he2,hroot,ht1,ht2,ht3]
    rw [he3]
    have hlast : base+(p.size+(1+((ps.map (fun p => p.size+4)).sum+1)))-1=
        base+(p.size+(1+(ps.map (fun p => p.size+4)).sum)) := by omega
    rw [hlast]


theorem disjoinClosingSuffix_length (ps : List (Formula ι)) (base endpoint : Nat) :
    (disjoinClosingSuffix base endpoint ps).length=3*ps.length := by
  induction ps generalizing base endpoint with
  | nil => rfl
  | cons p ps ih => simp [disjoinClosingSuffix,ih,Nat.mul_succ]

end ShiReversibleFormula
