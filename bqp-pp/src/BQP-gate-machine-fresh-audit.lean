import «BQP-gate-runs»
import «BQP-counted-runs»
import «BQP-bit-transfer»

#print axioms BQPCnot.compare_run
#print axioms BQPCnot.less_run
#print axioms BQPCnot.greater_run
#print axioms BQPCnot.from_indices
#print axioms BQPCnotParser.parse_pair
#print axioms BQPCnotParser.compiler_run
#print axioms BQPCnotParser.parse_emit_run
#print axioms BQPCnotParser.parse_emit_cost_le
#print axioms BQPGateDispatch.tag_run
#print axioms BQPGateDispatch.one_run
#print axioms BQPGateDispatch.two_run
#print axioms BQPGateDispatch.tagged_one_run
#print axioms BQPGateDispatch.tagged_two_run
#print axioms BQPCounted.delegate
#print axioms BQPCounted.header_run
#print axioms BQPCounted.repeat_run
#print axioms BQPCounted.counted_run
#print axioms BQPBitTransfer.transfer_run
