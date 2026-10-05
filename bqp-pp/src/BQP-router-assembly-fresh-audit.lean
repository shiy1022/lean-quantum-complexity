import «BQP-pair-fanout»
import «BQP-bool-ite»
import «BQP-final-inclusion»
#print axioms BQPPairCodec.decode_encode
#print axioms BQPPairCodec.decode_polyTime
#print axioms BQPPairFanout.pair_polyTime
#print axioms BQPBoolIte.polyTime

#print axioms BQPCheckerBoolean.ite
#print axioms BQPProgram.family_witness_pair_polyTime
#print axioms BQPProgram.longRelation_polyTime
#print axioms BQPFinal.bqp_subset_pp

example : ShiBQP.BQP ⊆ ShiClassPP.PP := BQPFinal.bqp_subset_pp

#print axioms ShiBQP.bqp_subset_pp
example : ShiBQP.BQP ⊆ ShiClassPP.PP := ShiBQP.bqp_subset_pp
