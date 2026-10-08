import ReversiblePaddedIteration
import ReversibleRawElementaryLayers

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {n : Nat}

/-- Repeated padded forests preserve the control-distinctness needed by exact Toffoli recovery. -/
theorem paddedIterationCompile_distinct_controls (ps : List (Formula (Fin n))) (hl : ps.length=n)
    (bound t : Nat) (inputs : Fin n → Nat) (base : Nat) :
    ∀ a ∈ paddedIterationCompile ps hl bound t inputs base,a.DistinctControls := by
  induction t generalizing inputs base with
  | zero => simp [paddedIterationCompile]
  | succ t ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact paddedForestCompile_distinct_controls ps inputs base bound a ha
    · exact ih _ _ a ha

/-- Count every actual elementary layer over the full runtime iteration history. -/
theorem paddedIterationCompile_layerCount (ps : List (Formula (Fin n))) (hl : ps.length=n)
    (bound t : Nat) (inputs : Fin n → Nat) (base : Nat) :
    ((paddedIterationCompile ps hl bound t inputs base).map rawAssignmentLayerCount).sum=
      t*((ps.map (fun p => formulaElementaryLayers p+1)).sum) := by
  induction t generalizing inputs base with
  | zero => simp only [paddedIterationCompile,List.map_nil,List.sum_nil,Nat.zero_mul]
  | succ t ih =>
    simp only [paddedIterationCompile,List.map_append,List.sum_append,paddedForestCompile_layerCount,ih,Nat.succ_mul]
    omega

end ShiReversibleGenerator
