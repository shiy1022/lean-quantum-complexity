import «BQP-checker-boolean»
import «BQP-family-majority»
import «BQP-router-threshold-checker»
import «BQP-router-witness-pieces»

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
namespace BQPProgram
open Turing BQPRouterArithmetic

/-- Preserve the actual instance while extracting either witness piece. -/
theorem family_witness_pair_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F)
    (keep : Bool) : Nonempty (TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1,BQPUnarySplit.result keep (2*(familyH F p.1+1)) p.2))) := by
  exact BQPPairFanout.pair_polyTime _ _ BQPChecked.reference3.2.2.1.1
    (family_witness_piece_polyTime F hu keep)

def bucketTest (F : ShiClass.Family) (i : Fin 5) (p : List Bool × List Bool) : Bool :=
  decide (BQPCounting.suffixValue (p.2.drop (2*(familyH F p.1+1))) <
    thresholdBound (familyH F p.1+1) i)

theorem bucketTest_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) (i : Fin 5) :
    PvsNP.PolyTimeChecker (bucketTest F i) := by
  have h := BQPGeneralPolyTime.comp (Sum.inl false) (family_witness_pair_polyTime F hu false)
    (family_threshold_checker_polyTime F hu i)
  exact h

noncomputable def innerResidue (F : ShiClass.Family) (d : ℕ) (p : List Bool × List Bool) : Bool :=
  BQPCounting.pairedPrefix (familyResidue checker F d) (p.1,p.2.take (2*(familyH F p.1+1)))

theorem innerResidue_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) (d : ℕ) :
    PvsNP.PolyTimeChecker (innerResidue F d) := by
  have h := BQPGeneralPolyTime.comp (Sum.inl false) (family_witness_pair_polyTime F hu true)
    (BQPFamilyPasses.normalized_family_polyTime checker F hu d)
  exact h

def balancedTail (F : ShiClass.Family) (p : List Bool × List Bool) : Bool :=
  (p.2.take (2*(familyH F p.1+1))).headI

theorem balancedTail_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeChecker (balancedTail F) := by
  have h := BQPGeneralPolyTime.comp false (family_inner_polyTime F hu)
    BQPCheckerBoolean.head_polyTime
  exact h

/-- The exact relation used by the counting proof has a constructed polynomial-time
machine. Only the original uniformity condition is assumed. -/
theorem longRelation_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeChecker (longRelation F) := by
  have h0 := innerResidue_polyTime F hu 0
  have h4 := BQPCheckerBoolean.not _ (innerResidue_polyTime F hu 4)
  have h1 := innerResidue_polyTime F hu 1
  have h3 := BQPCheckerBoolean.not _ (innerResidue_polyTime F hu 3)
  have ht := balancedTail_polyTime F hu
  have h := BQPCheckerBoolean.ite _ _ _ (bucketTest_polyTime F hu 0) h0
    (BQPCheckerBoolean.ite _ _ _ (bucketTest_polyTime F hu 1) h4
      (BQPCheckerBoolean.ite _ _ _ (bucketTest_polyTime F hu 2) h1
        (BQPCheckerBoolean.ite _ _ _ (bucketTest_polyTime F hu 3) h3
          (BQPCheckerBoolean.ite _ _ _ (bucketTest_polyTime F hu 4)
            (BQPCheckerBoolean.constant false) ht))))
  convert h using 1
  funext p
  simp [longRelation, BQPCounting.combinedChecker, bucketTest, thresholdBound,
    BQPCounting.suffixValue, innerResidue, balancedTail]

end BQPProgram
