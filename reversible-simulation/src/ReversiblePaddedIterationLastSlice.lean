import ReversiblePaddedIteration

set_option autoImplicit false
namespace ShiReversibleFormula
variable {n : Nat}

/-- Separate the last chronological slice without changing the compiler's actual assignments. -/
theorem paddedIterationCompile_succ_last (ps : List (Formula (Fin n))) (hl : ps.length=n)
    (bound t : Nat) (inputs : Fin n → Nat) (base : Nat) :
    paddedIterationCompile ps hl bound (t+1) inputs base=
      paddedIterationCompile ps hl bound t inputs base ++
      paddedForestCompile (paddedIterationRead ps hl bound t inputs base)
        (base+t*(n*(bound+1))) bound ps := by
  induction t generalizing inputs base with
  | zero => simp only [paddedIterationCompile,paddedIterationRead,List.append_nil,List.nil_append,Nat.zero_mul,Nat.add_zero]
  | succ t ih =>
    rw [paddedIterationCompile,ih]
    simp only [paddedIterationCompile,paddedIterationRead,List.append_assoc]
    have h : base+n*(bound+1)+t*(n*(bound+1))=base+(t+1)*(n*(bound+1)) := by ring
    rw [h]

end ShiReversibleFormula
