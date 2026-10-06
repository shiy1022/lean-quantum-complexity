/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.TesterCore
import QIP.ValidGates
import QIP.StrategyRealize

/-!
# Q20 — verifier testers and the interaction pairing

For a verifier description `d`, the **transition matrices** `transMat d j : W × Hist j` (with
`Hist j = Hist (Reg d) (Reg d) j`) collect, for every history `(x₀, y₀, …)`, the wire state
obtained by running the verifier blocks and inserting `|y_k⟩⟨x_k|` on message register `k`:

  `transMat d 0 = B₀ |0…0⟩`,   `transMat d (j+1) = B_{j+1} · transfer (transMat d j)`.

* `stateAfterBlock_eq`: for **every** prover `P` (arbitrary memory, entangled with the
  messages), the global state after block `j` is `(A_j ⊗ 1) · memState P j · (A_j ⊗ 1)ᴴ`.
  Here `memState` is the link-product state of `QIP.StrategyRealization`.
* The **tester** `tester d = A_mᴴ E A_m` (`E` the accepting effect) is PSD (`tester_posSemidef`)
  and depends only on `d`.
* **`accept_eq_pairing`**: `accept P = Re tr (tester d · stratOp P m)` for every prover.
* **`pairing_mem_Icc`**: `0 ≤ Re tr (tester d · Q) ≤ 1` for **every** causal strategy operator
  `Q`, through the realization theorem of Q19.

Only the definitions of `QIP.Execution` are used; no compatibility hypothesis is assumed.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable (d : Desc)

/-- The wire split at message register `j`: `Qubits W ≃ Rest × Reg`. -/
def wireSplitE (j : ℕ) : Qubits d.totalWires ≃ Rest d j × Reg d j :=
  (Equiv.piEquivPiSubtypeProd (inReg d j) (fun _ => Bool)).trans (Equiv.prodComm _ _)

theorem proverStep_eq_turnMap (P : Prover d) (j : ℕ) :
    proverStep P j = turnMap (wireSplitE d j) (P.act j) := rfl

/-- The transition matrices of the verifier. -/
noncomputable def transMat : ∀ j, Matrix (Qubits d.totalWires) (Hist (Reg d) (Reg d) j) ℂ
  | 0 => Matrix.of fun w _ => (blockMat d 0 *ᵥ zeroVec d.totalWires) w
  | j + 1 => blockMat d (j + 1) * transfer (wireSplitE d j) (transMat j)

/-- The accepting tester `A_mᴴ E A_m`. -/
noncomputable def tester : Matrix (Hist (Reg d) (Reg d) d.numMsgs) (Hist (Reg d) (Reg d) d.numMsgs) ℂ :=
  (transMat d d.numMsgs)ᴴ * basisEffect (outBit d) * transMat d d.numMsgs

theorem tester_posSemidef : (tester d).PosSemidef :=
  (isEffect_basisEffect (outBit d)).posSemidef.conjTranspose_mul_mul_same _

variable {d}

theorem conj_kron_one_mul {V V' K Mm : Type} [Fintype V] [Fintype K] [Fintype Mm]
    [DecidableEq Mm] (B : Matrix V' V ℂ) (A : Matrix V K ℂ) (R : Matrix (K × Mm) (K × Mm) ℂ) :
    (B ⊗ₖ (1 : Matrix Mm Mm ℂ)) * ((A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R * (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ) *
        (B ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ =
      ((B * A) ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R * ((B * A) ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ := by
  have hBA : (B * A) ⊗ₖ (1 : Matrix Mm Mm ℂ) =
      (B ⊗ₖ (1 : Matrix Mm Mm ℂ)) * (A ⊗ₖ (1 : Matrix Mm Mm ℂ)) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  rw [hBA, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem conjMap_pureState {V V' : Type} [Fintype V] (B : Matrix V' V ℂ) (v : V → ℂ) :
    conjMap B (pureState v) = pureState (B *ᵥ v) := by
  rw [conjMap_apply, pureState, mul_vecMulVec, vecMulVec_mul, pureState, star_mulVec]

/-- **The global state in transition-vector form**, for every prover. -/
theorem stateAfterBlock_eq (P : Prover d) : ∀ j ≤ d.numMsgs,
    stateAfterBlock P j =
      (transMat d j ⊗ₖ (1 : Matrix (P.M j) (P.M j) ℂ)) * memState P j *
        (transMat d j ⊗ₖ (1 : Matrix (P.M j) (P.M j) ℂ))ᴴ
  | 0, _ => by
    have hU : Unique (Hist (Reg d) (Reg d) 0) := inferInstanceAs (Unique Unit)
    ext ⟨w, μ⟩ ⟨w', μ'⟩
    rw [conjKron_apply, stateAfterBlock, initState, verifierStep_kronecker, kroneckerMap_apply,
      conjMap_pureState, Fintype.sum_unique, Fintype.sum_unique]
    simp only [pureState, vecMulVec_apply, Pi.star_apply, transMat, of_apply]
    change _ = _ * P.init μ μ' * _
    ring
  | j + 1, hj => by
    rw [stateAfterBlock, proverStep_eq_turnMap, stateAfterBlock_eq P j (by omega), turn_conj]
    rw [verifierStep, conjMap_apply, conj_kron_one_mul]
    rfl

/-- **The interaction pairing**: acceptance is the trace pairing of the tester with the
prover's strategy operator. -/
theorem accept_eq_pairing (P : Prover d) :
    accept P = (trace (tester d * stratOp P d.numMsgs)).re := by
  rw [accept, finalState, stateAfterBlock_eq P _ le_rfl, prob, acceptEffect, stratOp,
    trace_mul_traceRight, tester]
  congr 1
  set Mm := P.M d.numMsgs
  set A := transMat d d.numMsgs
  set E := basisEffect (outBit d)
  set R := memState P d.numMsgs
  have e1 : (E ⊗ₖ (1 : Matrix Mm Mm ℂ)) * ((A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R *
      (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ) =
      ((E ⊗ₖ (1 : Matrix Mm Mm ℂ)) * (A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R) *
        (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ := by simp only [Matrix.mul_assoc]
  have e2 : (A ⊗ₖ (1 : Matrix Mm Mm ℂ))ᴴ * ((E ⊗ₖ (1 : Matrix Mm Mm ℂ)) *
      (A ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R) = ((Aᴴ * E * A) ⊗ₖ (1 : Matrix Mm Mm ℂ)) * R := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  rw [e1, trace_mul_comm, e2]

/-- **Tester normalization**: the pairing lies in `[0, 1]` for every causal strategy operator. -/
theorem pairing_mem_Icc {Q : ∀ k, Matrix (Hist (Reg d) (Reg d) k) (Hist (Reg d) (Reg d) k) ℂ}
    (hQ : IsStrategy d.numMsgs Q) : (trace (tester d * Q d.numMsgs)).re ∈ Set.Icc 0 1 := by
  obtain ⟨S, -, hS⟩ := exists_opStrategy_of_isStrategy hQ
  rw [← hS _ le_rfl, ← accept_eq_pairing (d := d) S]
  exact accept_mem_Icc S

end ShiQIP
