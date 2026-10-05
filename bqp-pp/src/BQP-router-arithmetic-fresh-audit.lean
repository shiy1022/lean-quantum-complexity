import «BQP-router-threshold-values»
import «BQP-binary-add-pair»
import «BQP-pair-generation»
import «BQP-router-threshold-polytime»
import «BQP-binary-compare-pair»
import «BQP-router-threshold-checker»
import «BQP-unary-split»
import «BQP-router-witness-pieces»
#print axioms BQPBinaryAdd.add_correct
#print axioms BQPBinaryAdd.add_length
#print axioms BQPBinaryAdd.add_run
#print axioms BQPRouterArithmetic.bits_value
#print axioms BQPRouterArithmetic.thresholds_value
#print axioms BQPRouterArithmetic.thresholds_length

#print axioms BQPBinaryAddPair.pair_run
#print axioms BQPBinaryAddPair.polyTime

#print axioms BQPPairDuplicate.polyTime
#print axioms BQPPairSwap.polyTime
#print axioms BQPPairGeneration.pair_polyTime

#print axioms BQPRouterArithmetic.family_threshold_polyTime
#print axioms BQPBinaryComparePair.pair_run
#print axioms BQPBinaryComparePair.less_polyTime

#print axioms BQPRouterArithmetic.threshold_compare_correct
#print axioms BQPRouterArithmetic.family_threshold_checker_polyTime

#print axioms BQPUnarySplit.pair_run
#print axioms BQPUnarySplit.polyTime

#print axioms BQPRouterArithmetic.family_split_count_polyTime
#print axioms BQPRouterArithmetic.family_inner_polyTime
#print axioms BQPRouterArithmetic.family_suffix_polyTime
