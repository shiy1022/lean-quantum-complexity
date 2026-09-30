import «AMPUNI-centered-uniform»
import «AMPUNI-final»
import «AMPUNI-recovered-reference-validation»
import «AMPUNI-reference-rebuild»

set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

-- Generated reference mapping; all reconstructed declarations are kernel-checked.
run_cmd do
  let mut replacements : Array (Lean.Name × Lean.Name) := #[
      (``PvsNP.polyTimeComputable_comp, ``QMAReferenceValidation.candidate0),
      (``ShiBQP.polyBound_three_phase_compose, ``QMAReferenceValidation.candidate1),
      (``ShiClassQMAAmpX.ampFamilyX_resource_identities_and_regularity, ``QMAReferenceValidation.candidate2),
      (``ShiClassQMAAmpX.ampFamilyX_semantically_eq_ampFamily, ``QMAReferenceValidation.candidate3),
      (``ShiClassQMAAmp.ampFamily_resource_identities_and_depth, ``QMAReferenceValidation.candidate4),
      (``ShiClassQMAAmp.ampFamily_threefold_structure_package, ``QMAReferenceValidation.candidate5),
      (``ShiClassQMA.acceptWith_eq_majority_weight_before_readout, ``QMAReferenceValidation.candidate6),
      (``ShiClassQMA.acceptWith_eq_quadratic_form, ``QMAReferenceValidation.candidate7),
      (``ShiClassQMA.amplified_acceptWith_le_maj3_of_single_copy_bound, ``QMAReferenceValidation.candidate8),
      (``ShiClassQMA.amplifier_prefix_action_is_spread, ``QMAReferenceValidation.candidate9),
      (``ShiClassQMA.exists_amplified_witness_maj3_ge_of_single_copy_bound, ``QMAReferenceValidation.candidate10),
      (``ShiClassQMA.exists_amplifier_three_block_embedding, ``QMAReferenceValidation.candidate11),
      (``ShiClassQMA.exists_threefold_amplifier_structure_at_output_wires, ``QMAReferenceValidation.candidate12),
      (``ShiClassQMA.exists_witnessInputState_isometry, ``QMAReferenceValidation.candidate13),
      (``ShiClassQMA.exists_witness_space_acceptance_operator, ``QMAReferenceValidation.candidate14),
      (``ShiClassQMA.fanout_replicates_input_across_copies, ``QMAReferenceValidation.candidate15),
      (``ShiClassQMA.polyBounded_of_affine_depth_size_bounds, ``QMAReferenceValidation.candidate16),
      (``ShiClassQMA.wellFormed_amplified_pullback_fanout_decomposition, ``QMAReferenceValidation.candidate17),
      (``ShiClassQMA.witnessInputState_isometry_entries_and_threefold_action, ``QMAReferenceValidation.candidate18),
      (``ShiEmbed.embedCirc_depth_append_comp, ``QMAReferenceValidation.candidate19),
      (``ShiEmbed.layerOk_closure_append_embedCirc, ``QMAReferenceValidation.candidate20),
      (``ShiShallow.acceptOperator_isHermitian, ``QMAReferenceValidation.candidate21),
      (``ShiShallow.apply1_eq_apply1Matrix_mulVec, ``QMAReferenceValidation.candidate22),
      (``ShiShallow.apply1_tMat_eq_phase, ``QMAReferenceValidation.candidate23),
      (``ShiShallow.ccz_phase_exponent_eq, ``QMAReferenceValidation.candidate24),
      (``ShiShallow.circMatrix_unitary, ``QMAReferenceValidation.candidate25),
      (``ShiShallow.cnotState_eq_cnotMatrix_mulVec, ``QMAReferenceValidation.candidate26),
      (``ShiShallow.cnot_conj_phase_map, ``QMAReferenceValidation.candidate27),
      (``ShiShallow.conj_majority_inclusion_exclusion_of_unitary, ``QMAReferenceValidation.candidate28),
      (``ShiShallow.eigenvalues_le_of_quadratic_form_le, ``QMAReferenceValidation.candidate29),
      (``ShiShallow.eigenvalues_nonneg_of_quadratic_form_nonneg, ``QMAReferenceValidation.candidate30),
      (``ShiShallow.exists_fanout_embedded_pullback, ``QMAReferenceValidation.candidate31),
      (``ShiShallow.exists_layout_bijection, ``QMAReferenceValidation.candidate32),
      (``ShiShallow.exists_majority_readout_at_wires_layerOk_depth, ``QMAReferenceValidation.candidate33),
      (``ShiShallow.exists_sum_form_eigenbasis, ``QMAReferenceValidation.candidate34),
      (``ShiShallow.exists_toffoli_at_wires_layerOk_depth, ``QMAReferenceValidation.candidate35),
      (``ShiShallow.exists_width_cast_reindexing_isometry, ``QMAReferenceValidation.candidate36),
      (``ShiShallow.explicit_embedded_fanout_circuit, ``QMAReferenceValidation.candidate37),
      (``ShiShallow.explicit_toffoli_majority_readout_and_fanout_circuits, ``QMAReferenceValidation.candidate38),
      (``ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core, ``QMAReferenceValidation.candidate39),
      (``ShiShallow.inv_sqrt_two_mul_self, ``QMAReferenceValidation.candidate40),
      (``ShiShallow.majority3_accum, ``QMAReferenceValidation.candidate41),
      (``ShiShallow.majority_readout_scratch_accept_weight_eq_majority_weight, ``QMAReferenceValidation.candidate42),
      (``ShiShallow.majority_weight_eq_conj_majority_quadratic_form, ``QMAReferenceValidation.candidate43),
      (``ShiShallow.mulVec_majority_inclusion_exclusion_of_common_eigenvector, ``QMAReferenceValidation.candidate44),
      (``ShiShallow.ofReal_norm_sq, ``QMAReferenceValidation.candidate45),
      (``ShiShallow.phase_composition, ``QMAReferenceValidation.candidate46),
      (``ShiShallow.product_eigenbasis_sum_form_three, ``QMAReferenceValidation.candidate47),
      (``ShiShallow.product_family_orthonormal_three, ``QMAReferenceValidation.candidate48),
      (``ShiShallow.product_family_parseval_three, ``QMAReferenceValidation.candidate49),
      (``ShiShallow.projOut_majority_inclusion_exclusion, ``QMAReferenceValidation.candidate50),
      (``ShiShallow.quadratic_form_majority_le_of_eigenbasis, ``QMAReferenceValidation.candidate51),
      (``ShiShallow.quadratic_form_transport_and_two_bridge, ``QMAReferenceValidation.candidate52),
      (``ShiShallow.runLayered_append_action_readout, ``QMAReferenceValidation.candidate53),
      (``ShiShallow.runLayered_eq_circMatrix_mulVec, ``QMAReferenceValidation.candidate54),
      (``ShiSpread.embedInstr_apply_spread, ``QMAReferenceValidation.candidate55),
      (``ShiSpread.runLayered_embedCirc_spread, ``QMAReferenceValidation.candidate56),
      (``ShiSpread.sum_spread_reindex_of_injective, ``QMAReferenceValidation.candidate57),
      (``ShiTM.branch_loop_transfers_prefix_until_symbol, ``QMAReferenceValidation.candidate58),
      (``ShiTM.comp_outputsInTime, ``QMAReferenceValidation.candidate59),
      (``ShiTM.copy_loop_transfers_stack, ``QMAReferenceValidation.candidate60),
      (``ShiTM.copy_phase_transfers_output_state, ``QMAReferenceValidation.candidate61),
      (``ShiTM.counted_loop_transfers_prefix_with_marks, ``QMAReferenceValidation.candidate62),
      (``ShiTM.encInstr_of_embedInstr_tag_preserved_index_remapped, ``QMAReferenceValidation.candidate63),
      (``ShiTM.encNat_parser_block, ``QMAReferenceValidation.candidate64),
      (``ShiTM.encoding_length_formulas_and_size_bound, ``QMAReferenceValidation.candidate65),
      (``ShiTM.exists_stepAux_stack_growth_bound, ``QMAReferenceValidation.candidate66),
      (``ShiTM.initList_haltList_comp, ``QMAReferenceValidation.candidate67),
      (``ShiTM.initList_haltList_laws, ``QMAReferenceValidation.candidate68),
      (``ShiTM.iterate_compM_one_simulation, ``QMAReferenceValidation.candidate69),
      (``ShiTM.iterate_compM_two_simulation, ``QMAReferenceValidation.candidate70),
      (``ShiTM.outputLength_le_of_outputsInTime, ``QMAReferenceValidation.candidate71),
      (``ShiTM.piece_list_reload_pass, ``QMAReferenceValidation.candidate72),
      (``ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact, ``QMAReferenceValidation.candidate73),
      (``ShiTM.stack_supplied_index_emitter_block, ``QMAReferenceValidation.candidate74),
      (``ShiTM.stepAux_trStmt_one_simulation, ``QMAReferenceValidation.candidate75),
      (``ShiTM.stepAux_trStmt_two_simulation, ``QMAReferenceValidation.candidate76),
      (``ShiTM.unary_count_to_dispatch_symbol, ``QMAReferenceValidation.candidate77),
      (``ShiTensor.accept_weight_or_form_eq_count_form_three_copies, ``QMAReferenceValidation.candidate78),
      (``ShiTensor.conjTranspose_majority_compression_three_blocks, ``QMAReferenceValidation.candidate79),
      (``ShiTensor.mulVec_block_extend_right_tensor_eigenvector, ``QMAReferenceValidation.candidate80),
      (``ShiTensor.mulVec_block_extend_tensor_eigenvector, ``QMAReferenceValidation.candidate81),
      (``ShiTensor.quadratic_form_three_block_majority_le_of_bound, ``QMAReferenceValidation.candidate82),
      (``ShiTensor.runLayered_embed_three_blocks, ``QMAReferenceValidation.candidate83),
      (``ShiTensor.sum_normSq_tensor_three, ``QMAReferenceValidation.candidate84),
      (``ShiTensor.sum_split_factor, ``QMAReferenceValidation.candidate85),
      (``ShiTensor.tensor_majority_three_accept_weight_closed_form, ``QMAReferenceValidation.candidate86),
      (``ShiTensor.tensor_split_append_inverse, ``QMAReferenceValidation.candidate87),
      (``ShiTensor.three_copy_acceptance_operators_are_block_liftings, ``QMAReferenceValidation.candidate88)
    ]
  -- Reuse kernel-checked reconstructions from the fixed-threshold endpoint.
  -- This avoids duplicate declarations and lets both endpoints be imported together.
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    let restored := Lean.Name.str `QMAReferenceRebuilt name.toString
    if env.contains restored then
      replacements := replacements.push (name, restored)
  Lean.Elab.Command.liftCoreM (QMAReferenceRebuild.closeTheorem ``ShiQMAGeneralGap.centered_gap_amplification `ShiQMAGeneralGap.centered_gap_amplification_closed replacements)

#print axioms ShiQMAGeneralGap.centered_gap_amplification_closed
