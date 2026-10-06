import QIP.Gen.Cut
import QIP.Bell.Run


/-!
# Q31 — turns local to the prover's side

A permutation of basis labels that keeps the kept wires and acts on the rest independently of
them, and an operator on the memory alone, are generalized turns (`exists_turn_perm`,
`exists_turn_mem`); products of turns are turns (`turnOp_mul`).
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped Kronecker

variable {d : Desc} {N : Type} [Fintype N] [DecidableEq N]

theorem pmat_mulVec {X : Type} [Fintype X] [DecidableEq X] (σ : X ≃ X) (u : X → ℂ) (a : X) :
    (pmat σ *ᵥ u) a = u (σ.symm a) := by
  simp only [mulVec, dotProduct, pmat, of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm a)]
  · simp
  · intro b _ hb; rw [if_neg]; intro h; exact hb (by rw [h, Equiv.symm_apply_apply])
  · simp

theorem pmat_mem {X : Type} [Fintype X] [DecidableEq X] (σ : X ≃ X) :
    pmat σ ∈ Matrix.unitaryGroup X ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (pmat_iso σ)

omit [DecidableEq N] in
theorem turnOp_mulVec {k : ℕ} (U : Matrix (PS d k × N) (PS d k × N) ℂ) (v : Qubits d.totalWires × N → ℂ) :
    turnOp U *ᵥ v = (((1 : Matrix (KS d k) (KS d k) ℂ) ⊗ₖ U) *ᵥ (v ∘ (gsplit d k N).symm)) ∘
      gsplit d k N := by
  rw [turnOp, submatrix_mulVec_equiv]

/-- **A permutation local to the prover's side is a turn.** -/
theorem exists_turn_perm (k : ℕ) (f : Qubits d.totalWires × N → Qubits d.totalWires × N)
    (hf : Function.Involutive f)
    (h1 : ∀ z, (gsplit d k N (f z)).1 = (gsplit d k N z).1)
    (h2 : ∀ z z', (gsplit d k N z).2 = (gsplit d k N z').2 →
      (gsplit d k N (f z)).2 = (gsplit d k N (f z')).2) :
    ∃ U ∈ Matrix.unitaryGroup (PS d k × N) ℂ, ∀ v, turnOp U *ᵥ v = v ∘ f := by
  let κ₀ : KS d k := fun _ => false
  let τ : PS d k × N → PS d k × N := fun p => (gsplit d k N (f ((gsplit d k N).symm (κ₀, p)))).2
  have hτf : ∀ z, gsplit d k N (f z) = ((gsplit d k N z).1, τ (gsplit d k N z).2) := by
    intro z
    refine Prod.ext (h1 z) (h2 _ _ ?_)
    simp
  have hτ : Function.Involutive τ := by
    intro p
    have e : (gsplit d k N).symm (κ₀, τ p) = f ((gsplit d k N).symm (κ₀, p)) := by
      rw [Equiv.symm_apply_eq, hτf]
      simp
    show (gsplit d k N (f ((gsplit d k N).symm (κ₀, τ p)))).2 = p
    rw [e, hf]
    simp
  refine ⟨pmat hτ.toPerm, pmat_mem _, fun v => ?_⟩
  rw [turnOp_mulVec]
  funext z
  simp only [Function.comp_apply]
  rw [show gsplit d k N z = ((gsplit d k N z).1, (gsplit d k N z).2) from rfl, one_kron_mulVec_apply,
    pmat_mulVec, Function.Involutive.toPerm_symm]
  exact congrArg v (by rw [Equiv.symm_apply_eq, hτf]; rfl)


/-- **An operator on the memory alone is a turn.** -/
theorem exists_turn_mem (k : ℕ) {P : Matrix N N ℂ} (hP : P ∈ Matrix.unitaryGroup N ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (PS d k × N) ℂ, ∀ v,
      turnOp U *ᵥ v = ((1 : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ) ⊗ₖ P) *ᵥ v := by
  refine ⟨(1 : Matrix (PS d k) (PS d k) ℂ) ⊗ₖ P, kronecker_mem_unitary (one_mem _) hP, fun v => ?_⟩
  rw [turnOp_mulVec]
  funext ⟨x, ν⟩
  simp only [Function.comp_apply]
  rw [gsplit_apply, one_kron_mulVec_apply, one_kron_mulVec_apply, one_kron_mulVec_apply]
  congr 1
  funext ν'
  rw [Function.comp_apply, gsplit_symm_apply]
  congr 2
  funext w
  split_ifs <;> rfl

/-- Products of turns. -/
theorem exists_turn_mul {k : ℕ} {F G : (Qubits d.totalWires × N → ℂ) → Qubits d.totalWires × N → ℂ}
    (hF : ∃ U ∈ Matrix.unitaryGroup (PS d k × N) ℂ, ∀ v, turnOp U *ᵥ v = F v)
    (hG : ∃ U ∈ Matrix.unitaryGroup (PS d k × N) ℂ, ∀ v, turnOp U *ᵥ v = G v) :
    ∃ U ∈ Matrix.unitaryGroup (PS d k × N) ℂ, ∀ v, turnOp U *ᵥ v = F (G v) := by
  obtain ⟨U, hU, hUF⟩ := hF
  obtain ⟨V, hV, hVG⟩ := hG
  exact ⟨U * V, Submonoid.mul_mem _ hU hV, fun v => by rw [turnOp_mul, ← mulVec_mulVec, hVG, hUF]⟩

theorem exists_turn_id (k : ℕ) :
    ∃ U ∈ Matrix.unitaryGroup (PS d k × N) ℂ, ∀ v : Qubits d.totalWires × N → ℂ, turnOp U *ᵥ v = v :=
  ⟨1, one_mem _, fun v => by
    rw [turnOp_mulVec, one_kronecker_one, one_mulVec]
    funext z; simp⟩


omit [Fintype N] [DecidableEq N] in
/-- **Register wires are never kept across their own turn.** -/
theorem not_kept_of_inReg {k : ℕ} {x : Fin d.totalWires} (hx : inReg d k x) : ¬ kept d k x := by
  unfold kept
  by_cases hp : toProverAt d k
  · rw [(held_reg_toP hp hx).2]; simp
  · rw [(held_reg_toV hp hx).1]; simp

end ShiQIP
