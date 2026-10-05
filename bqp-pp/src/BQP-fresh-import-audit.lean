import «BQP-closed-references»
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do

    let info ← getConstInfo ``BQPChecked.reference0
    let target ← getConstInfo ``PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing"
    let axs ← collectAxioms ``BQPChecked.reference0
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference1
    let target ← getConstInfo ``PvsNP.polyTimeComputable_comp
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: PvsNP.polyTimeComputable_comp"
    let axs ← collectAxioms ``BQPChecked.reference1
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED PvsNP.polyTimeComputable_comp; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference2
    let target ← getConstInfo ``PvsNP.polyTime_composition_and_alphabet_transport
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: PvsNP.polyTime_composition_and_alphabet_transport"
    let axs ← collectAxioms ``BQPChecked.reference2
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED PvsNP.polyTime_composition_and_alphabet_transport; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference3
    let target ← getConstInfo ``PvsNP.tagged_transducers_untaggers_and_projections
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: PvsNP.tagged_transducers_untaggers_and_projections"
    let axs ← collectAxioms ``BQPChecked.reference3
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED PvsNP.tagged_transducers_untaggers_and_projections; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference4
    let target ← getConstInfo ``ShiBQP.acceptance_agreement_for_the_route_a_compiled_program
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.acceptance_agreement_for_the_route_a_compiled_program"
    let axs ← collectAxioms ``BQPChecked.reference4
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.acceptance_agreement_for_the_route_a_compiled_program; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference5
    let target ← getConstInfo ``ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion"
    let axs ← collectAxioms ``BQPChecked.reference5
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference6
    let target ← getConstInfo ``ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership"
    let axs ← collectAxioms ``BQPChecked.reference6
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference7
    let target ← getConstInfo ``ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count"
    let axs ← collectAxioms ``BQPChecked.reference7
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference8
    let target ← getConstInfo ``ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor"
    let axs ← collectAxioms ``BQPChecked.reference8
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference9
    let target ← getConstInfo ``ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance"
    let axs ← collectAxioms ``BQPChecked.reference9
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference10
    let target ← getConstInfo ``ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership"
    let axs ← collectAxioms ``BQPChecked.reference10
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference11
    let target ← getConstInfo ``ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one"
    let axs ← collectAxioms ``BQPChecked.reference11
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference12
    let target ← getConstInfo ``ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two"
    let axs ← collectAxioms ``BQPChecked.reference12
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference13
    let target ← getConstInfo ``ShiBQP.one_polynomial_time_compiler_over_the_flat_encoding_composed_with_the_layer_stripping_transducer
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.one_polynomial_time_compiler_over_the_flat_encoding_composed_with_the_layer_stripping_transducer"
    let axs ← collectAxioms ``BQPChecked.reference13
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.one_polynomial_time_compiler_over_the_flat_encoding_composed_with_the_layer_stripping_transducer; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference14
    let target ← getConstInfo ``ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one"
    let axs ← collectAxioms ``BQPChecked.reference14
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference15
    let target ← getConstInfo ``ShiBQP.opcode_stream_head_safety_and_adjoint_blocks
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.opcode_stream_head_safety_and_adjoint_blocks"
    let axs ← collectAxioms ``BQPChecked.reference15
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.opcode_stream_head_safety_and_adjoint_blocks; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference16
    let target ← getConstInfo ``ShiBQP.polyBound_three_phase_compose
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.polyBound_three_phase_compose"
    let axs ← collectAxioms ``BQPChecked.reference16
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.polyBound_three_phase_compose; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference17
    let target ← getConstInfo ``ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders"
    let axs ← collectAxioms ``BQPChecked.reference17
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference18
    let target ← getConstInfo ``ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run"
    let axs ← collectAxioms ``BQPChecked.reference18
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference19
    let target ← getConstInfo ``ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase"
    let axs ← collectAxioms ``BQPChecked.reference19
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference20
    let target ← getConstInfo ``ShiBQP.string_level_compiler_output_budget_for_any_parser_pair
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.string_level_compiler_output_budget_for_any_parser_pair"
    let axs ← collectAxioms ``BQPChecked.reference20
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.string_level_compiler_output_budget_for_any_parser_pair; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference21
    let target ← getConstInfo ``ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities"
    let axs ← collectAxioms ``BQPChecked.reference21
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference22
    let target ← getConstInfo ``ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input"
    let axs ← collectAxioms ``BQPChecked.reference22
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference23
    let target ← getConstInfo ``ShiClassPP.gap_general_integer_linear_combination
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiClassPP.gap_general_integer_linear_combination"
    let axs ← collectAxioms ``BQPChecked.reference23
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiClassPP.gap_general_integer_linear_combination; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference24
    let target ← getConstInfo ``ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings"
    let axs ← collectAxioms ``BQPChecked.reference24
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference25
    let target ← getConstInfo ``ShiClassPP.patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiClassPP.patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality"
    let axs ← collectAxioms ``BQPChecked.reference25
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiClassPP.patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference26
    let target ← getConstInfo ``ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches"
    let axs ← collectAxioms ``BQPChecked.reference26
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference27
    let target ← getConstInfo ``ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core"
    let axs ← collectAxioms ``BQPChecked.reference27
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference28
    let target ← getConstInfo ``ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch"
    let axs ← collectAxioms ``BQPChecked.reference28
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference29
    let target ← getConstInfo ``ShiTM.comp_outputsInTime
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.comp_outputsInTime"
    let axs ← collectAxioms ``BQPChecked.reference29
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.comp_outputsInTime; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference30
    let target ← getConstInfo ``ShiTM.copy_loop_transfers_stack
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.copy_loop_transfers_stack"
    let axs ← collectAxioms ``BQPChecked.reference30
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.copy_loop_transfers_stack; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference31
    let target ← getConstInfo ``ShiTM.copy_phase_transfers_output_state
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.copy_phase_transfers_output_state"
    let axs ← collectAxioms ``BQPChecked.reference31
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.copy_phase_transfers_output_state; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference32
    let target ← getConstInfo ``ShiTM.exists_stepAux_stack_growth_bound
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.exists_stepAux_stack_growth_bound"
    let axs ← collectAxioms ``BQPChecked.reference32
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.exists_stepAux_stack_growth_bound; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference33
    let target ← getConstInfo ``ShiTM.initList_haltList_comp
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.initList_haltList_comp"
    let axs ← collectAxioms ``BQPChecked.reference33
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.initList_haltList_comp; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference34
    let target ← getConstInfo ``ShiTM.initList_haltList_laws
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.initList_haltList_laws"
    let axs ← collectAxioms ``BQPChecked.reference34
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.initList_haltList_laws; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference35
    let target ← getConstInfo ``ShiTM.integer_square_root_machine_for_the_router_thresholds
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.integer_square_root_machine_for_the_router_thresholds"
    let axs ← collectAxioms ``BQPChecked.reference35
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.integer_square_root_machine_for_the_router_thresholds; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference36
    let target ← getConstInfo ``ShiTM.iterate_compM_one_simulation
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.iterate_compM_one_simulation"
    let axs ← collectAxioms ``BQPChecked.reference36
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.iterate_compM_one_simulation; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference37
    let target ← getConstInfo ``ShiTM.iterate_compM_two_simulation
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.iterate_compM_two_simulation"
    let axs ← collectAxioms ``BQPChecked.reference37
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.iterate_compM_two_simulation; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference38
    let target ← getConstInfo ``ShiTM.outputLength_le_of_outputsInTime
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.outputLength_le_of_outputsInTime"
    let axs ← collectAxioms ``BQPChecked.reference38
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.outputLength_le_of_outputsInTime; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference39
    let target ← getConstInfo ``ShiTM.outputsInTime_of_run_to_halt
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.outputsInTime_of_run_to_halt"
    let axs ← collectAxioms ``BQPChecked.reference39
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.outputsInTime_of_run_to_halt; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference40
    let target ← getConstInfo ``ShiTM.polyTimeComputable_of_machine_polybound
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.polyTimeComputable_of_machine_polybound"
    let axs ← collectAxioms ``BQPChecked.reference40
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.polyTimeComputable_of_machine_polybound; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference41
    let target ← getConstInfo ``ShiTM.stepAux_trStmt_one_simulation
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.stepAux_trStmt_one_simulation"
    let axs ← collectAxioms ``BQPChecked.reference41
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.stepAux_trStmt_one_simulation; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference42
    let target ← getConstInfo ``ShiTM.stepAux_trStmt_two_simulation
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.stepAux_trStmt_two_simulation"
    let axs ← collectAxioms ``BQPChecked.reference42
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.stepAux_trStmt_two_simulation; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference43
    let target ← getConstInfo ``ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside"
    let axs ← collectAxioms ``BQPChecked.reference43
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference44
    let target ← getConstInfo ``ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run"
    let axs ← collectAxioms ``BQPChecked.reference44
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run; axioms {axs}"

    let info ← getConstInfo ``BQPChecked.reference45
    let target ← getConstInfo ``ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts
    unless info.levelParams.length == target.levelParams.length do
      throwError "Fresh-import universe mismatch"
    let tp := info.type.instantiateLevelParams info.levelParams (target.levelParams.map Level.param)
    unless ← isDefEq tp target.type do
      throwError "Fresh-import statement mismatch: ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts"
    let axs ← collectAxioms ``BQPChecked.reference45
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Fresh-import unexpected axiom {ax}"
    logInfo m!"BQP_FRESH_IMPORT_CHECKED ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts; axioms {axs}"
