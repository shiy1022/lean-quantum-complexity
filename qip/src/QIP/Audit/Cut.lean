import QIP.Gen.Cut

/-! Fresh-import audit for Q30 (cut states and stitching): statement types, then transitive
axioms. -/

open ShiQIP ShiQuantum Matrix
open scoped Kronecker ComplexOrder

#check (cut_bound : ∀ {d : Desc} {N : Type} [Fintype N] [DecidableEq N], d.Valid →
  ∀ {c : ℕ}, c < d.numMsgs → ∀ (UF UB : Turns d N),
    (∀ k, UF k ∈ Matrix.unitaryGroup (PS d k × N) ℂ) →
    (∀ k, UB k ∈ Matrix.unitaryGroup (PS d k × N) ℂ) →
    ∀ (ξ : Qubits d.totalWires × N → ℂ), nsq ξ = 1 →
      fwdP UF c ξ + bwdP UB c ξ ≤ 1 + Real.sqrt (value d))
#check (exists_unitary_overlap_eq_fidelity : ∀ {n E : Type} [Fintype n] [DecidableEq n]
  [Fintype E] [DecidableEq E] {ρ σ : Matrix n n ℂ}, ρ.PosSemidef → σ.PosSemidef →
    ∀ {ψ φ : n × E → ℂ}, IsPurification ψ ρ → IsPurification φ σ → ∀ (e₀ : E) (a₀ : n),
      ∃ W ∈ Matrix.unitaryGroup (E × n) ℂ,
        star (addAnc a₀ φ) ⬝ᵥ (((1 : Matrix n n ℂ) ⊗ₖ W) *ᵥ addAnc a₀ ψ) = (fidelity ρ σ : ℂ))

#print axioms ShiQuantum.addAnc
#print axioms ShiQuantum.putEnv
#print axioms ShiQuantum.isPurification_addAnc
#print axioms ShiQuantum.isPurification_putEnv
#print axioms ShiQuantum.dot_putEnv
#print axioms ShiQuantum.exists_unitary_overlap_eq_fidelity
#print axioms ShiQIP.blockOp
#print axioms ShiQIP.turnOp
#print axioms ShiQIP.Turns
#print axioms ShiQIP.preOp
#print axioms ShiQIP.sufOp
#print axioms ShiQIP.preOp_add
#print axioms ShiQIP.gturn_eq
#print axioms ShiQIP.gRun_eq_preOp
#print axioms ShiQIP.blockOp_mem
#print axioms ShiQIP.turnOp_mem
#print axioms ShiQIP.preOp_mem
#print axioms ShiQIP.sufOp_mem
#print axioms ShiQIP.nsq
#print axioms ShiQIP.dot_self_eq_nsq
#print axioms ShiQIP.nsq_nonneg
#print axioms ShiQIP.dot_mulVec_adj
#print axioms ShiQIP.nsq_unitary
#print axioms ShiQIP.nsq_smul
#print axioms ShiQIP.fwd_overlap
#print axioms ShiQIP.margK
#print axioms ShiQIP.margK_posSemidef
#print axioms ShiQIP.dot_comp_equiv
#print axioms ShiQIP.isDensity_margK
#print axioms ShiQIP.norm_dot_le_fidelity
#print axioms ShiQIP.projQ
#print axioms ShiQIP.projQ_apply
#print axioms ShiQIP.projQ_conjTranspose
#print axioms ShiQIP.projQ_mul_self
#print axioms ShiQIP.nsq_projQ
#print axioms ShiQIP.gAcc_eq_nsq
#print axioms ShiQIP.Zero0
#print axioms ShiQIP.fwdP
#print axioms ShiQIP.bwdP
#print axioms ShiQIP.fwd_bound
#print axioms ShiQIP.bwd_bound
#print axioms ShiQIP.norm_dot_sq_le
#print axioms ShiQIP.liftVec
#print axioms ShiQIP.liftM
#print axioms ShiQIP.liftM_mem
#print axioms ShiQIP.nsq_liftVec
#print axioms ShiQIP.dot_liftVec
#print axioms ShiQIP.blockOp_liftVec
#print axioms ShiQIP.turnOp_liftM
#print axioms ShiQIP.turnOp_liftVec
#print axioms ShiQIP.turnOp_mul
#print axioms ShiQIP.projQ_liftVec
#print axioms ShiQIP.uTurn
#print axioms ShiQIP.stTurns
#print axioms ShiQIP.uTurn_mem
#print axioms ShiQIP.stTurns_lt
#print axioms ShiQIP.stTurns_gt
#print axioms ShiQIP.stTurns_c
#print axioms ShiQIP.preOp_stTurns
#print axioms ShiQIP.sufOp_lift
#print axioms ShiQIP.sufOp_stTurns
#print axioms ShiQIP.turnOp_uhl
#print axioms ShiQIP.liftVec_comp_symm
#print axioms ShiQIP.stitch
#print axioms ShiQIP.nsq_projQ_le
#print axioms ShiQIP.cut_bound
