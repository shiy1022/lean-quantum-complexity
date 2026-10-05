import «BQP-all-candidates»
import «AMPUNI-reference-rebuild»

set_option maxHeartbeats 40000000
set_option maxRecDepth 30000

open Lean in
def bqpCloseReferences (roots replacements : Array (Name × Name)) : CoreM Unit := do
  let initial : QMAReferenceRebuild.State := {
    replacements := Std.HashMap.ofList replacements.toList }
  let action : QMAReferenceRebuild.M Unit := do
    for (original, result) in roots do
      let info ← getConstInfo original
      let closed ← QMAReferenceRebuild.rebuild original
      addDecl <| .thmDecl {
        name := result
        levelParams := info.levelParams
        type := info.type
        value := mkConst closed (info.levelParams.map Level.param)
      }
      let axioms ← collectAxioms result
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected BQP reference axiom {ax} in {result}"
      logInfo m!"BQP_REFERENCE_CLOSED {original} as {result}; axioms {axioms}"
  let (_, state) ← action.run initial
  logInfo m!"BQP_RECONSTRUCTION_COUNT {state.count}"
  for (original, rebuilt) in state.rebuilt.toList do
    logInfo m!"BQP_REBUILT_LINK {original} => {rebuilt}"

run_cmd do
  let roots : Array (Lean.Name × Lean.Name) := #[
    (``PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing, `BQPChecked.reference0),
    (``PvsNP.polyTimeComputable_comp, `BQPChecked.reference1),
    (``PvsNP.polyTime_composition_and_alphabet_transport, `BQPChecked.reference2),
    (``PvsNP.tagged_transducers_untaggers_and_projections, `BQPChecked.reference3),
    (``ShiBQP.acceptance_agreement_for_the_route_a_compiled_program, `BQPChecked.reference4),
    (``ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion, `BQPChecked.reference5),
    (``ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership, `BQPChecked.reference6),
    (``ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count, `BQPChecked.reference7),
    (``ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor, `BQPChecked.reference8),
    (``ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance, `BQPChecked.reference9),
    (``ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership, `BQPChecked.reference10),
    (``ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one, `BQPChecked.reference11),
    (``ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two, `BQPChecked.reference12),
    (``ShiBQP.one_polynomial_time_compiler_over_the_flat_encoding_composed_with_the_layer_stripping_transducer, `BQPChecked.reference13),
    (``ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one, `BQPChecked.reference14),
    (``ShiBQP.opcode_stream_head_safety_and_adjoint_blocks, `BQPChecked.reference15),
    (``ShiBQP.polyBound_three_phase_compose, `BQPChecked.reference16),
    (``ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders, `BQPChecked.reference17),
    (``ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run, `BQPChecked.reference18),
    (``ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase, `BQPChecked.reference19),
    (``ShiBQP.string_level_compiler_output_budget_for_any_parser_pair, `BQPChecked.reference20),
    (``ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities, `BQPChecked.reference21),
    (``ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input, `BQPChecked.reference22),
    (``ShiClassPP.gap_general_integer_linear_combination, `BQPChecked.reference23),
    (``ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings, `BQPChecked.reference24),
    (``ShiClassPP.patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality, `BQPChecked.reference25),
    (``ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches, `BQPChecked.reference26),
    (``ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core, `BQPChecked.reference27),
    (``ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch, `BQPChecked.reference28),
    (``ShiTM.comp_outputsInTime, `BQPChecked.reference29),
    (``ShiTM.copy_loop_transfers_stack, `BQPChecked.reference30),
    (``ShiTM.copy_phase_transfers_output_state, `BQPChecked.reference31),
    (``ShiTM.exists_stepAux_stack_growth_bound, `BQPChecked.reference32),
    (``ShiTM.initList_haltList_comp, `BQPChecked.reference33),
    (``ShiTM.initList_haltList_laws, `BQPChecked.reference34),
    (``ShiTM.integer_square_root_machine_for_the_router_thresholds, `BQPChecked.reference35),
    (``ShiTM.iterate_compM_one_simulation, `BQPChecked.reference36),
    (``ShiTM.iterate_compM_two_simulation, `BQPChecked.reference37),
    (``ShiTM.outputLength_le_of_outputsInTime, `BQPChecked.reference38),
    (``ShiTM.outputsInTime_of_run_to_halt, `BQPChecked.reference39),
    (``ShiTM.polyTimeComputable_of_machine_polybound, `BQPChecked.reference40),
    (``ShiTM.stepAux_trStmt_one_simulation, `BQPChecked.reference41),
    (``ShiTM.stepAux_trStmt_two_simulation, `BQPChecked.reference42),
    (``ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside, `BQPChecked.reference43),
    (``ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run, `BQPChecked.reference44),
    (``ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts, `BQPChecked.reference45)
  ]
  let replacements : Array (Lean.Name × Lean.Name) := #[
    (``PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing, ``BQPReferenceValidation.candidate0),
    (``PvsNP.polyTimeComputable_comp, ``BQPReferenceValidation.candidate1),
    (``PvsNP.polyTime_composition_and_alphabet_transport, ``BQPReferenceValidation.candidate2),
    (``PvsNP.tagged_transducers_untaggers_and_projections, ``BQPReferenceValidation.candidate3),
    (``ShiBQP.acceptance_agreement_for_the_route_a_compiled_program, ``BQPReferenceValidation.candidate4),
    (``ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion, ``BQPReferenceValidation.candidate5),
    (``ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership, ``BQPReferenceValidation.candidate6),
    (``ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count, ``BQPReferenceValidation.candidate7),
    (``ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor, ``BQPReferenceValidation.candidate8),
    (``ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance, ``BQPReferenceValidation.candidate9),
    (``ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership, ``BQPReferenceValidation.candidate10),
    (``ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one, ``BQPReferenceValidation.candidate11),
    (``ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two, ``BQPReferenceValidation.candidate12),
    (``ShiBQP.one_polynomial_time_compiler_over_the_flat_encoding_composed_with_the_layer_stripping_transducer, ``BQPReferenceValidation.candidate13),
    (``ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one, ``BQPReferenceValidation.candidate14),
    (``ShiBQP.opcode_stream_head_safety_and_adjoint_blocks, ``BQPReferenceValidation.candidate15),
    (``ShiBQP.polyBound_three_phase_compose, ``BQPReferenceValidation.candidate16),
    (``ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders, ``BQPReferenceValidation.candidate17),
    (``ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run, ``BQPReferenceValidation.candidate18),
    (``ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase, ``BQPReferenceValidation.candidate19),
    (``ShiBQP.string_level_compiler_output_budget_for_any_parser_pair, ``BQPReferenceValidation.candidate20),
    (``ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities, ``BQPReferenceValidation.candidate21),
    (``ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input, ``BQPReferenceValidation.candidate22),
    (``ShiClassPP.gap_general_integer_linear_combination, ``BQPReferenceValidation.candidate23),
    (``ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings, ``BQPReferenceValidation.candidate24),
    (``ShiClassPP.patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality, ``BQPReferenceValidation.candidate25),
    (``ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches, ``BQPReferenceValidation.candidate26),
    (``ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core, ``BQPReferenceValidation.candidate27),
    (``ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch, ``BQPReferenceValidation.candidate28),
    (``ShiTM.comp_outputsInTime, ``BQPReferenceValidation.candidate29),
    (``ShiTM.copy_loop_transfers_stack, ``BQPReferenceValidation.candidate30),
    (``ShiTM.copy_phase_transfers_output_state, ``BQPReferenceValidation.candidate31),
    (``ShiTM.exists_stepAux_stack_growth_bound, ``BQPReferenceValidation.candidate32),
    (``ShiTM.initList_haltList_comp, ``BQPReferenceValidation.candidate33),
    (``ShiTM.initList_haltList_laws, ``BQPReferenceValidation.candidate34),
    (``ShiTM.integer_square_root_machine_for_the_router_thresholds, ``BQPReferenceValidation.candidate35),
    (``ShiTM.iterate_compM_one_simulation, ``BQPReferenceValidation.candidate36),
    (``ShiTM.iterate_compM_two_simulation, ``BQPReferenceValidation.candidate37),
    (``ShiTM.outputLength_le_of_outputsInTime, ``BQPReferenceValidation.candidate38),
    (``ShiTM.outputsInTime_of_run_to_halt, ``BQPReferenceValidation.candidate39),
    (``ShiTM.polyTimeComputable_of_machine_polybound, ``BQPReferenceValidation.candidate40),
    (``ShiTM.stepAux_trStmt_one_simulation, ``BQPReferenceValidation.candidate41),
    (``ShiTM.stepAux_trStmt_two_simulation, ``BQPReferenceValidation.candidate42),
    (``ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside, ``BQPReferenceValidation.candidate43),
    (``ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run, ``BQPReferenceValidation.candidate44),
    (``ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts, ``BQPReferenceValidation.candidate45)
  ]
  Lean.Elab.Command.liftCoreM (bqpCloseReferences roots replacements)

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference0
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE PvsNP.combined_checker_is_polynomial_time_via_the_lossless_pairing | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference1
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE PvsNP.polyTimeComputable_comp | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference2
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE PvsNP.polyTime_composition_and_alphabet_transport | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference3
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE PvsNP.tagged_transducers_untaggers_and_projections | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference4
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.acceptance_agreement_for_the_route_a_compiled_program | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference5
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.acceptance_as_integer_pair_counts_and_a_decidable_threshold_criterion | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference6
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.acceptance_in_the_ring_adjoining_root_two_decides_pp_membership | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference7
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.accepting_sum_of_squared_path_amplitudes_is_a_common_endpoint_pair_count | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference8
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.digit_by_digit_integer_square_root_and_bit_serial_subtractor | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference9
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.doubled_program_single_run_count_equals_the_ordered_pair_count_with_instance | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference10
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.explicit_combined_checker_and_the_conditional_pp_membership | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference11
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.gate_predicate_counts_are_polynomially_dominated_above_length_one_and_provably_not_at_zero_or_one | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference12
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.modulus_squared_of_eighth_root_sum_lies_in_the_ring_adjoining_root_two | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference13
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.one_polynomial_time_compiler_over_the_flat_encoding_composed_with_the_layer_stripping_transducer | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference14
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.one_polynomial_time_transducer_carrying_the_layered_encoding_to_the_flat_one | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference15
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.opcode_stream_head_safety_and_adjoint_blocks | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference16
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.polyBound_three_phase_compose | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference17
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.polyTimeComputable_bridge_for_generic_pairing_decoders | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference18
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.polyTimeComputable_string_level_compiler_from_an_affinely_bounded_run | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference19
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.single_run_checker_is_polynomial_time_and_counts_branches_by_phase | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference20
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.string_level_compiler_output_budget_for_any_parser_pair | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference21
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.the_string_level_compiler_over_the_flat_gate_encoding_with_its_decode_and_parse_identities | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference22
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiBQP.uniform_family_encoding_is_polynomial_time_computable_from_the_input | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference23
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiClassPP.gap_general_integer_linear_combination | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference24
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiClassPP.majority_counting_at_witness_lengths_zero_and_one_and_membership_from_long_inputs_plus_the_three_short_strings | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference25
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiClassPP.patching_a_polynomial_time_checker_to_constants_on_the_three_shortest_instances_from_conjunction_and_equality | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference26
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiShallow.circuit_amplitude_is_a_path_sum_over_hadamard_branches | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference27
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference28
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.a_compiler_host_machine_with_a_fuel_drain_and_a_total_three_way_gate_dispatch | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference29
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.comp_outputsInTime | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference30
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.copy_loop_transfers_stack | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference31
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.copy_phase_transfers_output_state | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference32
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.exists_stepAux_stack_growth_bound | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference33
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.initList_haltList_comp | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference34
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.initList_haltList_laws | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference35
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.integer_square_root_machine_for_the_router_thresholds | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference36
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.iterate_compM_one_simulation | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference37
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.iterate_compM_two_simulation | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference38
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.outputLength_le_of_outputsInTime | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference39
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.outputsInTime_of_run_to_halt | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference40
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.polyTimeComputable_of_machine_polybound | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference41
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.stepAux_trStmt_one_simulation | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference42
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.stepAux_trStmt_two_simulation | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference43
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.the_compiler_run_for_every_input_over_the_flat_parser_seam_with_truncation_routed_aside | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference44
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.the_compiler_run_for_every_input_with_the_ill_formed_branch_discharged_as_a_machine_run | {d.userName} | {tp}"

open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let info ← getConstInfo ``BQPChecked.reference45
    forallTelescope info.type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          let tp ← ppExpr d.type
          logInfo m!"BQP_OUTER_PREMISE ShiTM.the_mirrored_gate_loop_with_a_fifth_arm_skipping_records_whose_tag_no_renderer_accepts | {d.userName} | {tp}"
