import «AMPUNI-selector-circuit»
import «AMPUNI-threshold-interface»

/-! Concrete general-threshold family: resources, normalized witness semantics,
and approximate centering. Uniform circuit generation remains a separate obligation. -/

/-! ## AMPUNI-centering-family -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace ShiQMACenteringCircuit
open ShiShallow ShiEmbed ShiSpread ShiClassQMA

/-- The complete centering circuit adds only the suffix depth. -/
theorem centeredCircuit_depth_le {m : Nat} (c : Layered m) (out : Fin m) (bs : List Bool) :
    depth (centeredCircuit c out bs) ≤ depth c + 77 * bs.length + 76 := by
  have hs := centeringSuffix_depth_le m out bs
  simp only [centeredCircuit, depth, List.length_append, embedCirc, List.length_map] at *
  omega

theorem centeredCircuit_wellFormed {m : Nat} (c : Layered m) (out : Fin m) (bs : List Bool)
    (hc : ∀ l ∈ c, LayerOk l) : ∀ l ∈ centeredCircuit c out bs, LayerOk l := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · exact (QMAReferenceValidation.candidate20 (Fin.castAdd (3 * bs.length + 3))
      (Fin.castAdd_injective _ _)).1 c hc l h
  · exact centeringSuffix_wellFormed m out bs l h

abbrev centeringExtra (bs : List Bool) : Nat := 3 * bs.length + 3

theorem centeredWidth (F : QMAFamily) (n : Nat) (bs : List Bool) :
    (n + (F.wit n + (F.anc n + 1))) + centeringExtra bs =
      n + (F.wit n + ((F.anc n + centeringExtra bs) + 1)) := by omega

/-- A concrete verifier family, with the original witness register unchanged.
Uniform generation is deliberately not asserted by this definition. -/
abbrev centeredFamily (F : QMAFamily) (bits : Nat → List Bool) : QMAFamily where
  anc n := F.anc n + centeringExtra (bits n)
  wit := F.wit
  circ n := embedCirc (Fin.cast (centeredWidth F n (bits n)))
    (Fin.cast_injective _) (centeredCircuit (F.circ n) (F.out n) (bits n))
  out n := Fin.cast (centeredWidth F n (bits n))
    ⟨n + (F.wit n + (F.anc n + 1)) + 3 * (bits n).length + 2, by
      dsimp [centeringExtra]; omega⟩

theorem centeredFamily_witness (F : QMAFamily) (bits : Nat → List Bool) (n : Nat) :
    (centeredFamily F bits).wit n = F.wit n := rfl

theorem centeredFamily_ancillas (F : QMAFamily) (bits : Nat → List Bool) (n : Nat) :
    (centeredFamily F bits).anc n = F.anc n + 3 * (bits n).length + 3 := by
  simp only [centeredFamily, centeringExtra]; omega

theorem centeredFamily_depth (F : QMAFamily) (bits : Nat → List Bool) (n : Nat) :
    depth ((centeredFamily F bits).circ n) ≤ depth (F.circ n) + 77 * (bits n).length + 76 := by
  change (embedCirc (Fin.cast (centeredWidth F n (bits n))) (Fin.cast_injective _)
    (centeredCircuit (F.circ n) (F.out n) (bits n))).length ≤ _
  simp only [embedCirc, List.length_map]
  exact centeredCircuit_depth_le (F.circ n) (F.out n) (bits n)

theorem centeredFamily_wellFormed (F : QMAFamily) (bits : Nat → List Bool)
    (hF : ShiBQP.WellFormed F.toFamily) : ShiBQP.WellFormed (centeredFamily F bits).toFamily := by
  intro n l hl
  exact (QMAReferenceValidation.candidate20 (Fin.cast (centeredWidth F n (bits n)))
    (Fin.cast_injective _)).1 _
    (centeredCircuit_wellFormed (F.circ n) (F.out n) (bits n) (hF n)) l hl

theorem centeredFamily_polyBounded (F : QMAFamily) (bits : Nat → List Bool)
    (hF : ShiBQP.PolyBounded F.toFamily) (p : Polynomial ℕ)
    (hbits : ∀ n, (bits n).length ≤ p.eval n) :
    ShiBQP.PolyBounded (centeredFamily F bits).toFamily := by
  obtain ⟨q, hd, ha⟩ := hF
  refine ⟨q + 77 * p + 76, ?_, ?_⟩
  · intro n
    change depth ((centeredFamily F bits).circ n) ≤ _
    apply (centeredFamily_depth F bits n).trans
    have hq : depth (F.circ n) ≤ q.eval n := hd n
    have hp := hbits n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    omega
  · intro n
    change F.wit n + (F.anc n + (3 * (bits n).length + 3)) ≤ _
    have hq : F.wit n + F.anc n ≤ q.eval n := ha n
    have hp := hbits n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    omega

end ShiQMACenteringCircuit

open Lean Elab Command in
run_cmd do
  for name in #[``ShiQMACenteringCircuit.centeredCircuit_wellFormed,
      ``ShiQMACenteringCircuit.centeredFamily_witness,
      ``ShiQMACenteringCircuit.centeredFamily_ancillas,
      ``ShiQMACenteringCircuit.centeredFamily_depth,
      ``ShiQMACenteringCircuit.centeredFamily_wellFormed,
      ``ShiQMACenteringCircuit.centeredFamily_polyBounded] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-family axiom {ax} in {name}"
    logInfo m!"CENTERING_FAMILY_RESOURCES_CHECKED {name}; axioms {axioms}"

/-! ## AMPUNI-centering-norm -/

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

namespace ShiQMACenteringNorm
open ShiShallow ShiClassQMA

private lemma shiHc_bridge {m : ℕ} (u : QState m) :
    ((∑ y : Bits m, ‖u y‖ ^ 2 : ℝ) : ℂ) = ∑ y : Bits m, star (u y) * u y := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun y _ => ShiShallow.ofReal_norm_sq (u y))

private lemma shiHc_sum_normSq_mulVec {K M : ℕ}
    (W : Matrix (Bits K) (Bits M) ℂ)
    (hW : Matrix.conjTranspose W * W = (1 : Op M)) (v : QState M) :
    ∑ y : Bits K, ‖Matrix.mulVec W v y‖ ^ 2 = ∑ z : Bits M, ‖v z‖ ^ 2 := by
  have hcol : ∀ b d : Bits M,
      (∑ y : Bits K, star (W y b) * W y d) = (if b = d then (1 : ℂ) else 0) := by
    intro b d
    have h := congrFun (congrFun hW b) d
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    exact h
  have key : ∀ y : Bits K, star (Matrix.mulVec W v y) * Matrix.mulVec W v y
      = ∑ b : Bits M, ∑ d : Bits M, (star (W y b) * W y d) * (star (v b) * v d) := by
    intro y
    have hmv : Matrix.mulVec W v y = ∑ b : Bits M, W y b * v b := by
      simp only [Matrix.mulVec, dotProduct]
    rw [hmv, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [star_mul']
    ring
  refine Complex.ofReal_injective ?_
  rw [shiHc_bridge, shiHc_bridge]
  calc ∑ y : Bits K, star (Matrix.mulVec W v y) * Matrix.mulVec W v y
      = ∑ y : Bits K, ∑ b : Bits M, ∑ d : Bits M,
          (star (W y b) * W y d) * (star (v b) * v d) :=
        Finset.sum_congr rfl (fun y _ => key y)
    _ = ∑ b : Bits M, ∑ d : Bits M, ∑ y : Bits K,
          (star (W y b) * W y d) * (star (v b) * v d) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ b : Bits M, ∑ d : Bits M,
          (if b = d then (1 : ℂ) else 0) * (star (v b) * v d) := by
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun d _ => ?_))
        rw [← Finset.sum_mul, hcol b d]
    _ = ∑ b : Bits M, star (v b) * v b := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hterm : ∀ d : Bits M, (if b = d then (1 : ℂ) else 0) * (star (v b) * v d)
            = (if b = d then star (v b) * v b else 0) := by
          intro d
          by_cases hbd : b = d
          · rw [if_pos hbd, if_pos hbd, one_mul, hbd]
          · rw [if_neg hbd, if_neg hbd, zero_mul]
        rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_ite_eq]
        rw [if_pos (Finset.mem_univ b)]

theorem source_run_norm {N : ℕ} (cc : Layered N) (v : QState N) :
    ∑ y : Bits N, ‖runLayered cc v y‖ ^ 2 = ∑ z : Bits N, ‖v z‖ ^ 2 := by
  have hu : Matrix.conjTranspose (ShiShallow.circMatrix cc) * ShiShallow.circMatrix cc
      = (1 : Op N) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact ShiShallow.circMatrix_unitary cc
  rw [ShiShallow.runLayered_eq_circMatrix_mulVec
      (fun U i w => ShiShallow.apply1_eq_apply1Matrix_mulVec U i w)
      (fun i j hij w => ShiShallow.cnotState_eq_cnotMatrix_mulVec i j hij w) cc v]
  exact shiHc_sum_normSq_mulVec (ShiShallow.circMatrix cc) hu v


theorem source_input_norm {n : Nat} (F : QMAFamily) (x : Bits n) (ψ : QState (F.wit n)) :
    (∑ y, ‖witnessInputState F x ψ y‖ ^ 2) = ∑ z, ‖ψ z‖ ^ 2 := by
  obtain ⟨V, hViso, hVact⟩ := ShiClassQMA.exists_witnessInputState_isometry F x
  rw [← hVact ψ]
  exact shiHc_sum_normSq_mulVec V hViso ψ

end ShiQMACenteringNorm

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
  let roots : Array (Lean.Name × Lean.Name) := #[
    (``ShiQMACenteringNorm.source_run_norm, `ShiQMACenteringNorm.run_norm),
    (``ShiQMACenteringNorm.source_input_norm, `ShiQMACenteringNorm.input_norm)]
  for (original, result) in roots do
    Lean.Elab.Command.liftCoreM (QMACenteringReferenceRebuild.closeTheorem original result replacements)

#print axioms ShiQMACenteringNorm.run_norm
#print axioms ShiQMACenteringNorm.input_norm

/-! ## AMPUNI-centering-family-semantics -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace ShiQMACenteringCircuit
open ShiShallow ShiEmbed ShiSpread ShiClassQMA

private theorem spread_cast {m n : Nat} (h : m = n) (ψ : QState m) (y : Bits n) :
    spread (Fin.cast h) ψ y = ψ (fun i => y (Fin.cast h i)) := by
  subst n
  have ho : ∀ k : Fin m, OffImage (Fin.cast rfl) k → y k = false := by
    intro k hk
    exact (hk k rfl).elim
  unfold spread
  rw [if_pos ho]
  rfl

private theorem spread_castAdd {m r : Nat} (ψ : QState m) (y : Bits (m + r)) :
    spread (Fin.castAdd r) ψ y =
      if ∀ i : Fin (m + r), m ≤ i.val → y i = false then
        ψ (fun i => y (Fin.castAdd r i)) else 0 := by
  have hi (i : Fin (m + r)) : OffImage (Fin.castAdd r) i ↔ m ≤ i.val := by
    constructor
    · intro h
      by_contra hn
      have hv : i.val < m := by omega
      exact h ⟨i.val, hv⟩ (Fin.ext rfl)
    · intro h j he
      have hv := congrArg Fin.val he
      have hj := j.isLt
      simp only [Fin.val_castAdd] at hv
      omega
  simp only [spread, hi]
  rfl

private theorem witnessInputState_numeric {n : Nat} (F : QMAFamily) (x : Bits n)
    (ψ : QState (F.wit n)) (y : Bits (n + (F.wit n + (F.anc n + 1)))) :
    witnessInputState F x ψ y =
      if (∀ i : Fin n, y (Fin.castAdd (F.wit n + (F.anc n + 1)) i) = x i) ∧
        (∀ i : Fin (n + (F.wit n + (F.anc n + 1))), n + F.wit n ≤ i.val → y i = false)
      then ψ (fun j => y (Fin.natAdd n (Fin.castAdd (F.anc n + 1) j))) else 0 := by
  have ha : (∀ l : Fin (F.anc n + 1),
      y (Fin.natAdd n (Fin.natAdd (F.wit n) l)) = false) ↔
      (∀ i : Fin (n + (F.wit n + (F.anc n + 1))), n + F.wit n ≤ i.val → y i = false) := by
    constructor
    · intro h i hi
      let l : Fin (F.anc n + 1) := ⟨i.val - (n + F.wit n), by have := i.isLt; omega⟩
      have he : Fin.natAdd n (Fin.natAdd (F.wit n) l) = i := by
        apply Fin.ext
        dsimp [l]
        omega
      simpa only [he] using h l
    · intro h l
      exact h _ (by simp only [Fin.val_natAdd]; omega)
  simp only [witnessInputState, ha]

/-- Padding the family really appends zero ancillas to its witness input;
this identifies the concrete family with the finite-register circuit theorem. -/
theorem centeredFamily_input (F : QMAFamily) (bits : Nat → List Bool) {n : Nat}
    (x : Bits n) (ψ : QState (F.wit n)) :
    witnessInputState (centeredFamily F bits) x ψ =
      spread (Fin.cast (centeredWidth F n (bits n)))
        (spread (Fin.castAdd (centeringExtra (bits n))) (witnessInputState F x ψ)) := by
  classical
  funext y
  rw [spread_cast, spread_castAdd, witnessInputState_numeric]
  let m := n + (F.wit n + (F.anc n + 1))
  let r := centeringExtra (bits n)
  let h := centeredWidth F n (bits n)
  let e : Fin m → Fin (n + (F.wit n + ((F.anc n + r) + 1))) :=
    fun i => Fin.cast h (Fin.castAdd r i)
  have hz : (∀ i : Fin (n + (F.wit n + ((F.anc n + r) + 1))),
      n + F.wit n ≤ i.val → y i = false) ↔
      (∀ i : Fin (m + r), m ≤ i.val → y (Fin.cast h i) = false) ∧
      (∀ i : Fin m, n + F.wit n ≤ i.val → y (e i) = false) := by
    constructor
    · intro ha
      constructor
      · intro i hi
        exact ha _ (by dsimp [m] at hi; simpa only [Fin.val_cast] using (show n + F.wit n ≤ i.val by omega))
      · intro i hi
        exact ha _ hi
    · rintro ⟨ha, hb⟩ i hi
      by_cases hm : i.val < m
      · have he : e ⟨i.val, hm⟩ = i := Fin.ext rfl
        simpa only [he] using hb ⟨i.val, hm⟩ hi
      · let j : Fin (m + r) := ⟨i.val, by have := i.isLt; dsimp [m, r]; omega⟩
        have he : Fin.cast h j = i := Fin.ext rfl
        simpa only [he] using ha j (by dsimp [j]; omega)
  rw [witnessInputState_numeric]
  change (if (∀ i : Fin n, y (Fin.castAdd _ i) = x i) ∧
      (∀ i : Fin (n + (F.wit n + ((F.anc n + r) + 1))),
        n + F.wit n ≤ i.val → y i = false) then _ else 0) = _
  simp only [hz]
  let P : Prop := ∀ i : Fin n,
    y (Fin.castAdd (F.wit n + ((F.anc n + r) + 1)) i) = x i
  let O : Prop := ∀ i : Fin (m + r), m ≤ i.val → y (Fin.cast h i) = false
  let A : Prop := ∀ i : Fin m, n + F.wit n ≤ i.val → y (e i) = false
  let v : ℂ := ψ (fun j => y (Fin.natAdd n (Fin.castAdd ((F.anc n + r) + 1) j)))
  change (if P ∧ (O ∧ A) then v else 0) = if O then (if P ∧ A then v else 0) else 0
  by_cases hp : P <;> by_cases ho : O <;> by_cases ha : A <;>
    simp only [hp, ho, ha, and_true, true_and, and_false, false_and, ↓reduceIte]

end ShiQMACenteringCircuit

namespace ShiQMACenteringCircuit
open ShiShallow ShiEmbed ShiSpread ShiClassQMA ShiQMACenteredGap

/-- The finite circuit formula transported to the actual QMA family.
This identity is homogeneous and therefore holds even for unnormalized witnesses. -/
theorem centeredFamily_accept_weight (F : QMAFamily) (bits : Nat → List Bool) {n : Nat}
    (x : Bits n) (ψ : QState (F.wit n)) :
    (centeredFamily F bits).acceptWith x ψ =
      (F.acceptWith x ψ + dyadicValue (bits n) *
        (∑ y, ‖runLayered (F.circ n) (witnessInputState F x ψ) y‖ ^ 2)) / 2 := by
  unfold QMAFamily.acceptWith
  rw [centeredFamily_input]
  change (∑ y, if y (Fin.cast (centeredWidth F n (bits n))
      ⟨n + (F.wit n + (F.anc n + 1)) + 3 * (bits n).length + 2,
        by dsimp [centeringExtra]; omega⟩) then
      ‖runLayered (embedCirc (Fin.cast (centeredWidth F n (bits n))) (Fin.cast_injective _)
        (centeredCircuit (F.circ n) (F.out n) (bits n)))
        (spread (Fin.cast (centeredWidth F n (bits n)))
          (spread (Fin.castAdd (centeringExtra (bits n))) (witnessInputState F x ψ))) y‖ ^ 2
      else 0) = _
  rw [ShiQMACenteringReference.embedSpread]
  have hsum := ShiQMACenteringReference.sumSpread
    (Fin.cast (centeredWidth F n (bits n))) (Fin.cast_injective _)
    (runLayered (centeredCircuit (F.circ n) (F.out n) (bits n))
      (spread (Fin.castAdd (centeringExtra (bits n))) (witnessInputState F x ψ)))
    (fun z a => if z ⟨n + (F.wit n + (F.anc n + 1)) + 3 * (bits n).length + 2,
      by dsimp [centeringExtra]; omega⟩ then ‖a‖ ^ 2 else 0) (by intro z; simp)
  exact hsum.trans (centeredCircuit_accept_weight (F.circ n) (F.out n) (bits n)
    (witnessInputState F x ψ))

/-- The actual verifier implements the affine acceptance map for every
normalized witness, without assuming preservation of state norm. -/
theorem centeredFamily_accept (F : QMAFamily) (bits : Nat → List Bool) {n : Nat}
    (x : Bits n) (ψ : QState (F.wit n)) (hψ : Normalized ψ) :
    (centeredFamily F bits).acceptWith x ψ =
      centeredAcceptance (dyadicValue (bits n)) (F.acceptWith x ψ) := by
  rw [centeredFamily_accept_weight, ShiQMACenteringNorm.run_norm,
    ShiQMACenteringNorm.input_norm, hψ]
  simp only [centeredAcceptance, mul_one]

end ShiQMACenteringCircuit

open Lean Elab Command in
run_cmd do
  for name in #[``ShiQMACenteringCircuit.centeredFamily_input,
      ``ShiQMACenteringCircuit.centeredFamily_accept_weight,
      ``ShiQMACenteringCircuit.centeredFamily_accept] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected family-semantics axiom {ax} in {name}"
    logInfo m!"CENTERING_FAMILY_SEMANTICS_CHECKED {name}; axioms {axioms}"

/-! ## AMPUNI-general-gap-centered-family -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAGeneralGap
open ShiShallow ShiClassQMA ShiQMACenteringCircuit ShiQMACenteredGap ShiQMAConstructiveSchedule

/-- The concrete verifier obtained by computing a dyadic centering coin from
threshold approximation algorithms. Uniformity is a separate machine proof. -/
def thresholdFamily {a b : Nat → ℝ} (F : QMAFamily)
    (A : ThresholdApproximation a) (B : ThresholdApproximation b)
    (q : Polynomial ℕ) : QMAFamily :=
  centeredFamily F (thresholdCoinBits A B q)

theorem thresholdCoinBits_polyBound {a b : Nat → ℝ}
    (A : ThresholdApproximation a) (B : ThresholdApproximation b) (q : Polynomial ℕ) :
    ∃ p : Polynomial ℕ, ∀ n, (thresholdCoinBits A B q n).length ≤ p.eval n := by
  refine ⟨Polynomial.C (Nat.log 2 (q.eval 1 + 1) + 5) +
    Polynomial.C q.natDegree * (Polynomial.X + 2), ?_⟩
  intro n
  rw [thresholdCoinBits_length]
  have hl := Nat.log_le_self 2 (n + 1)
  have hm := Nat.mul_le_mul_left q.natDegree hl
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_ofNat]
  dsimp [rounds, exponentBudget]
  nlinarith

theorem thresholdFamily_verifies {a b : Nat → ℝ} (F : QMAFamily) (L : Language Bool)
    (A : ThresholdApproximation a) (B : ThresholdApproximation b) (q : Polynomial ℕ)
    (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, b n ≤ a n)
    (hgap : ∀ n, (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n))
    (hv : VerifiesWith F L a b) :
    VerifiesWith (thresholdFamily F A B q) L
      (fun n => 1 / 2 + (a n - b n) / 8) (fun n => 1 / 2 - (a n - b n) / 8) := by
  intro w
  have hcoin := thresholdCoinBits_spec A B q w.length (hb _) (hab _) (hgap _)
  have hc := approximate_centering hcoin
  constructor
  · intro hw
    obtain ⟨ψ, hψ, ha⟩ := (hv w).1 hw
    refine ⟨ψ, hψ, ?_⟩
    change 1 / 2 + (a w.length - b w.length) / 8 ≤
      (centeredFamily F (thresholdCoinBits A B q)).acceptWith (ShiBQP.toBits w) ψ
    rw [centeredFamily_accept F _ _ ψ hψ]
    exact hc.1 _ ha
  · intro hw ψ hψ
    change (centeredFamily F (thresholdCoinBits A B q)).acceptWith (ShiBQP.toBits w) ψ ≤ _
    rw [centeredFamily_accept F _ _ ψ hψ]
    exact hc.2 _ ((hv w).2 hw ψ hψ)

/-- The general-threshold centering construction has checked quantum semantics
and polynomial circuit resources. This theorem does not assume or assert a
polynomial-time encoding generator for the new family. -/
theorem thresholdFamily_semantics_and_resources {a b : Nat → ℝ}
    (F : QMAFamily) (L : Language Bool)
    (A : ThresholdApproximation a) (B : ThresholdApproximation b) (q : Polynomial ℕ)
    (hf : ShiBQP.WellFormed F.toFamily) (hp : ShiBQP.PolyBounded F.toFamily)
    (hb : ∀ n, 0 ≤ b n) (hab : ∀ n, b n ≤ a n)
    (hgap : ∀ n, (1 : ℝ) ≤ (↑(q.eval n) : ℝ) * (a n - b n))
    (hv : VerifiesWith F L a b) :
    ShiBQP.WellFormed (thresholdFamily F A B q).toFamily ∧
    ShiBQP.PolyBounded (thresholdFamily F A B q).toFamily ∧
    (∀ n, (thresholdFamily F A B q).wit n = F.wit n) ∧
    VerifiesWith (thresholdFamily F A B q) L
      (fun n => 1 / 2 + (a n - b n) / 8) (fun n => 1 / 2 - (a n - b n) / 8) := by
  obtain ⟨p, hbits⟩ := thresholdCoinBits_polyBound A B q
  exact ⟨centeredFamily_wellFormed F _ hf, centeredFamily_polyBounded F _ hp p hbits,
    fun _ => rfl, thresholdFamily_verifies F L A B q hb hab hgap hv⟩

end ShiQMAGeneralGap

open Lean Elab Command in
run_cmd do
  for name in #[``ShiQMAGeneralGap.thresholdCoinBits_polyBound,
      ``ShiQMAGeneralGap.thresholdFamily_verifies,
      ``ShiQMAGeneralGap.thresholdFamily_semantics_and_resources] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected general-gap family axiom {ax} in {name}"
    logInfo m!"GENERAL_GAP_CENTERING_FAMILY_CHECKED {name}; axioms {axioms}"

namespace ShiQMACenteringCircuit
open ShiShallow ShiEmbed ShiClassQMA ShiClassQMAU ShiBQP

private theorem encLayer_embed_val {m n : Nat} (e : Fin m → Fin n)
    (he : Function.Injective e) (hv : ∀ i, (e i).val = i.val) (l : List (Instr m)) :
    encLayer (embedLayer e he l) = encLayer l := by
  have hf : encInstr ∘ embedInstr e he = encInstr := by
    funext g
    cases g <;> simp only [Function.comp_apply, embedInstr, encInstr, hv]
  simp only [encLayer, embedLayer, List.map_map, hf]

private theorem encodedLayers_embed_val {m n : Nat} (e : Fin m → Fin n)
    (he : Function.Injective e) (hv : ∀ i, (e i).val = i.val) (c : Layered m) :
    (embedCirc e he c).map encLayer = c.map encLayer := by
  have hf : encLayer ∘ embedLayer e he = encLayer := by
    funext l
    exact encLayer_embed_val e he hv l
  simp only [embedCirc, List.map_map, hf]

private theorem encCirc_embed_val {m n : Nat} (e : Fin m → Fin n)
    (he : Function.Injective e) (hv : ∀ i, (e i).val = i.val) (c : Layered m) :
    encCirc (embedCirc e he c) = encCirc c := by
  simp only [encCirc, encodedLayers_embed_val e he hv]

/-- Prefix padding preserves every original gate code; only the circuit
length header changes and the new suffix is appended. -/
theorem centeredCircuit_encoding {m : Nat} (c : Layered m) (out : Fin m) (bs : List Bool) :
    encCirc (centeredCircuit c out bs) =
      encNat (depth c + depth (centeringSuffix m out bs)) ++
        (c.map encLayer).flatten ++ ((centeringSuffix m out bs).map encLayer).flatten := by
  simp only [centeredCircuit, encCirc, List.map_append, encStr,
    List.length_append, List.length_map, embedCirc, List.flatten_append, depth]
  have he := encodedLayers_embed_val (Fin.castAdd (3 * bs.length + 3))
    (Fin.castAdd_injective _ _) (fun _ => rfl) c
  simp only [embedCirc] at he
  rw [he]
  simp only [List.append_assoc]

/-- Exact serialized output required of the remaining uniform centering
machine. In particular it can copy the old circuit payload unchanged. -/
theorem centeredFamily_encoding (F : QMAFamily) (bits : Nat → List Bool) (n : Nat) :
    encQMAFamilyAt (centeredFamily F bits) n =
      encNat (F.wit n) ++ encNat (F.anc n + centeringExtra (bits n)) ++
        encNat (n + (F.wit n + (F.anc n + 1)) + 3 * (bits n).length + 2) ++
        (encNat (depth (F.circ n) + depth
            (centeringSuffix (n + (F.wit n + (F.anc n + 1))) (F.out n) (bits n))) ++
          ((F.circ n).map encLayer).flatten ++
          ((centeringSuffix (n + (F.wit n + (F.anc n + 1))) (F.out n) (bits n)).map encLayer).flatten) := by
  simp only [encQMAFamilyAt, centeredFamily, Fin.val_cast]
  rw [encCirc_embed_val (Fin.cast (centeredWidth F n (bits n)))
    (Fin.cast_injective _) (fun _ => rfl), centeredCircuit_encoding]

end ShiQMACenteringCircuit

open Lean Elab Command in
run_cmd do
  for name in #[``ShiQMACenteringCircuit.centeredCircuit_encoding,
      ``ShiQMACenteringCircuit.centeredFamily_encoding] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected centering-encoding axiom {ax} in {name}"
    logInfo m!"CENTERING_ENCODING_CHECKED {name}; axioms {axioms}"

namespace ShiQMACenteringCircuit
open ShiShallow

theorem coinStep_depth_exact {N : Nat} (w : Fin 4 → Fin N)
    (hw : Function.Injective w) (b : Bool) :
    depth (coinStep w hw b) = 76 + (if b then 1 else 0) := by
  have h : (fairSelectorCirc w hw).length = 76 := fairSelectorCirc_depth w hw
  cases b <;> simp [coinStep, depth, h]

theorem coinCircuit_depth_exact {N : Nat} (base : Nat) (bs : List Bool)
    (h : base + 3 * bs.length < N) :
    depth (coinCircuit base bs h) = 76 * bs.length + bs.count true := by
  induction bs with
  | nil => simp [coinCircuit, depth]
  | cons b bs ih =>
    have ht : base + 3 * bs.length < N := by simp only [List.length_cons] at h; omega
    have htail := ih ht
    have hs := coinStep_depth_exact (coinWires base bs.length h)
      (coinWires_injective base bs.length h) b
    simp only [coinCircuit, depth, List.length_append, List.length_cons] at *
    cases b <;> simp at hs ⊢ <;> omega

/-- Exact layer header required by the encoding generator. -/
theorem centeringSuffix_depth_exact (m : Nat) (out : Fin m) (bs : List Bool) :
    depth (centeringSuffix m out bs) = 76 * bs.length + bs.count true + 76 := by
  have hc := coinCircuit_depth_exact (N := m + (3 * bs.length + 3)) m bs (by omega)
  have hs := fairSelectorCirc_depth (centeringWires m bs.length out)
    (centeringWires_injective m bs.length out)
  simp only [centeringSuffix, depth, List.length_append] at *
  omega

end ShiQMACenteringCircuit

open Lean Elab Command in
run_cmd do
  let name := ``ShiQMACenteringCircuit.centeringSuffix_depth_exact
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected exact-size axiom {ax}"
  logInfo m!"CENTERING_EXACT_SIZE_CHECKED {name}; axioms {axioms}"
