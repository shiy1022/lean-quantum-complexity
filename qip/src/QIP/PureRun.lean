/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Purified
import Quantum.Completion

/-!
# Pure-state execution of isometric provers

Against an isometric prover (`QIP.Purified`), the global state of the interaction stays pure.
`pureRun T j` is the global state vector on the verifier wires and the prover memory just after
block `j`:

  `pureRun T 0 = (B₀ ⊗ 1) (|0…0⟩ ⊗ init)`,
  `pureRun T (j+1) = (B_{j+1} ⊗ 1) (turn j) (pureRun T j)`,

where turn `j` applies the prover isometry `V j` to register `j` and the memory
(`turnVec`).

* **`stateAfterBlock_pureRun`**: `stateAfterBlock T.toOp j = |pureRun T j⟩⟨pureRun T j|`;
* **`accept_pureRun`**: `accept T.toOp = ⟨ψ| E ⊗ 1 |ψ⟩` for the final vector `ψ`.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {d : Desc}

theorem submatrix_pureState {α β : Type} (v : α → ℂ) (e : β ≃ α) :
    (pureState v).submatrix e e = pureState (v ∘ e) := by
  ext a b; simp [pureState, vecMulVec_apply]

theorem kronecker_pureState {α β : Type} (v : α → ℂ) (w : β → ℂ) :
    pureState v ⊗ₖ pureState w = pureState (fun p : α × β => v p.1 * w p.2) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [pureState, vecMulVec_apply, kroneckerMap_apply, star_mul']; ring

/-- One prover turn on a global vector. -/
noncomputable def turnVec (T : IsoStrategy (Reg d) (Reg d) d.numMsgs) (j : ℕ)
    (v : Qubits d.totalWires × T.M j → ℂ) : Qubits d.totalWires × T.M (j + 1) → ℂ :=
  (((1 : Matrix (Rest d j) (Rest d j) ℂ) ⊗ₖ T.V j) *ᵥ (v ∘ (turnSplit d j (T.M j)).symm)) ∘
    turnSplit d j (T.M (j + 1))

theorem proverStep_pureState (T : IsoStrategy (Reg d) (Reg d) d.numMsgs) (j : ℕ)
    (v : Qubits d.totalWires × T.M j → ℂ) :
    proverStep T.toOp j (pureState v) = pureState (turnVec T j v) := by
  simp only [proverStep, LinearMap.comp_apply, reindexMap_apply, reindex_apply]
  rw [submatrix_pureState]
  change Matrix.submatrix (liftR (Rest d j) (conjMap (T.V j)) (pureState _)) _ _ = _
  rw [liftR_conjMap_pureState, submatrix_pureState]
  rfl

/-- **Pure execution against an isometric prover.** -/
noncomputable def pureRun (T : IsoStrategy (Reg d) (Reg d) d.numMsgs) :
    ∀ j, Qubits d.totalWires × T.M j → ℂ
  | 0 => (blockMat d 0 ⊗ₖ (1 : Matrix (T.M 0) (T.M 0) ℂ)) *ᵥ
      fun p => zeroVec d.totalWires p.1 * T.init p.2
  | j + 1 => (blockMat d (j + 1) ⊗ₖ (1 : Matrix (T.M (j + 1)) (T.M (j + 1)) ℂ)) *ᵥ
      turnVec T j (pureRun T j)

/-- **The global state is pure.** -/
theorem stateAfterBlock_pureRun (T : IsoStrategy (Reg d) (Reg d) d.numMsgs) :
    ∀ j, stateAfterBlock T.toOp j = pureState (pureRun T j)
  | 0 => by
    rw [stateAfterBlock, initState, verifierStep]
    change conjMap _ (pureState (zeroVec d.totalWires) ⊗ₖ pureState T.init) = _
    rw [kronecker_pureState, conjMap_pureState]
    rfl
  | j + 1 => by
    rw [stateAfterBlock, stateAfterBlock_pureRun T j, proverStep_pureState, verifierStep,
      conjMap_pureState]
    rfl

/-- **Acceptance against an isometric prover**, as an expectation in the final vector. -/
theorem accept_pureRun (T : IsoStrategy (Reg d) (Reg d) d.numMsgs) :
    accept T.toOp = (star (pureRun T d.numMsgs) ⬝ᵥ
      (acceptEffect d (T.M d.numMsgs) *ᵥ pureRun T d.numMsgs)).re := by
  rw [accept, finalState, stateAfterBlock_pureRun, prob_pureState]

end ShiQIP
