import «BQP-typed-polytime»
import «BQP-header-field»
import «BQP-skip-one-header»
import «BQP-string-primitives»
import «BQP-bit-blocks-outputs»
import «BQP-family-fields»

#print axioms BQPTypedPolyTime.comp
#print axioms BQPTypedPolyTime.precompose
#print axioms BQPHeaderField.field_run
#print axioms BQPHeaderField.polyTime
#print axioms BQPHeaderField.count_unary
#print axioms BQPSkipHeaders.one_outputs
#print axioms BQPSkipHeaders.one_polyTime
#print axioms BQPStringPrimitives.prefix_polyTime
#print axioms BQPStringPrimitives.rename_polyTime
#print axioms BQPBitBlocks.polyTime
#print axioms BQPProgram.load_polyTime
#print axioms BQPProgram.endpoint_polyTime
#print axioms BQPProgram.return_polyTime
#print axioms BQPFamilyPasses.description_polyTime
#print axioms BQPFamilyPasses.circuit_polyTime
#print axioms BQPFamilyPasses.forward_polyTime
#print axioms BQPFamilyPasses.adjoint_polyTime
#print axioms BQPFamilyPasses.anc_polyTime
#print axioms BQPFamilyPasses.out_polyTime
#print axioms BQPFamilyPasses.output_test_polyTime
#print axioms BQPFamilyPasses.padding_polyTime
