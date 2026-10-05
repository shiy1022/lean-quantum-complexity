import «BQP-router-threshold-polytime»
import «BQP-binary-compare-pair»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPRouterArithmetic
open Turing BQPProgram

def thresholdBound (h : ℕ) (i : Fin 5) : ℕ :=
  (![2^(h+4), 2*2^(h+4),
    2*2^(h+4)+2*Nat.sqrt (2*4^(h+3)),
    2*2^(h+4)+4*Nat.sqrt (2*4^(h+3)),
    2*2^(h+4)+4*Nat.sqrt (2*4^(h+3))+16] : Fin 5 → ℕ) i

theorem threshold_compare_correct (h : ℕ) (i : Fin 5) (s : List Bool) :
    BQPBinaryCompare.borrow s (thresholds h i) false =
      decide (BQPCounting.suffixValue s < thresholdBound h i) := by
  rw [BQPBinaryCompare.compare_correct, ← value_eq_suffixValue (thresholds h i), thresholds_value]
  rfl

/-- Compute the family threshold while preserving an arbitrary suffix, then compare
all suffix bits. No length restriction, truncation, or preloaded input assumption. -/
theorem family_threshold_checker_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F)
    (i : Fin 5) : PvsNP.PolyTimeChecker
      (fun p : List Bool × List Bool =>
        decide (BQPCounting.suffixValue p.2 < thresholdBound (familyH F p.1+1) i)) := by
  have h1 := BQPMapFirst.map_first_polyTime _ (family_threshold_polyTime F hu i)
  have h2 := BQPGeneralPolyTime.comp (Sum.inl false) h1 BQPPairSwap.polyTime
  have h3 := BQPGeneralPolyTime.comp (Sum.inl false) h2 BQPBinaryComparePair.polyTime
  simpa only [PvsNP.PolyTimeChecker, Function.comp_def, threshold_compare_correct] using h3

end BQPRouterArithmetic
