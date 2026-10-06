/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.CircuitSemantics
import QIP.Resources
import QIP.StrategyRealization

/-!
# Q15 — operational interaction

The interaction of a verifier description `d : Desc` (`QIP.Syntax`) with a prover.

**Global system.** The `W = d.totalWires` verifier wires (`Qubits W`), followed by the prover's
private memory. Initially every wire is `|0⟩`, and the memory is in a prover-chosen density
operator `init`, uncorrelated with the wires (`initState`).

**Message registers.** Message `j` owns the wires `msgOffset j ≤ w < msgOffset j + width j`
(`inReg`), with basis `Reg d j`. No private wire lies in any message register
(`inReg_ge_priv`).

**Prover.** A prover is an operational strategy (`QIP.StrategyRealization`) whose turn `j` has
input and output register `Reg d j`:

  `Prover d = OpStrategy (Reg d) (Reg d) d.numMsgs`,

with **arbitrary** finite memories `M j`, an initial memory state, and channels
`act j : Reg d j × M j → Reg d j × M (j + 1)`. Turn `j` takes place after verifier block `j`,
and the prover acts on register `j` and its memory only (`proverStep`):

* message `j` prover → verifier: the prover receives the fresh `|0⟩` register, which carries no
  information, and returns the message;
* message `j` verifier → prover: the prover receives the message and may write anything back.
  Valid descriptions never let the verifier act on a register after sending it, so whatever is
  written back cannot influence acceptance.

Every other wire, in particular every private wire, is untouched (`proverStep_marginal`:
no-signalling). There is exactly one prover turn per message, and its input and output
registers are explicit. This is the form in which Q20 relates acceptance to strategy operators.

**Verifier.** Block `j` is the unitary `layerMat` of its gates (`Gate.toInstr?` to
`ShiShallow.Instr`, then `QIP.GateMatrix`), tensored with the identity on the memory.

* `final_isDensity`: the final state is a density operator;
* `accept_mem_Icc`: the acceptance probability lies in `[0, 1]`.

No bound is placed on the prover's circuit complexity or memory dimension.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Message registers -/

/-- The width of message `j` (zero beyond the last message). -/
def Desc.msgWidth (d : Desc) (j : ℕ) : ℕ := ((d.msgs[j]?).map Message.width).getD 0

/-- Wire `w` belongs to message register `j`. -/
def inReg (d : Desc) (j : ℕ) (w : Fin d.totalWires) : Prop :=
  d.msgOffset j ≤ w ∧ (w : ℕ) < d.msgOffset j + d.msgWidth j

instance (d : Desc) (j : ℕ) : DecidablePred (inReg d j) := fun _ => by
  unfold inReg; infer_instance

/-- **No private wire lies in a message register.** -/
theorem inReg_ge_priv {d : Desc} {j : ℕ} {w : Fin d.totalWires} (h : inReg d j w) :
    d.priv ≤ w := by
  have : d.priv ≤ d.msgOffset j := Nat.le_add_right _ _
  exact this.trans h.1

/-- The basis of message register `j`. -/
abbrev Reg (d : Desc) (j : ℕ) : Type := {w : Fin d.totalWires // inReg d j w} → Bool

/-- The basis of the wires outside message register `j`. -/
abbrev Rest (d : Desc) (j : ℕ) : Type := {w : Fin d.totalWires // ¬ inReg d j w} → Bool

/-- `Qubits W × Mem ≃ Rest × (Reg × Mem)`. -/
def turnSplit (d : Desc) (j : ℕ) (Mem : Type) :
    Qubits d.totalWires × Mem ≃ Rest d j × (Reg d j × Mem) :=
  (((Equiv.piEquivPiSubtypeProd (inReg d j) (fun _ => Bool)).trans
    (Equiv.prodComm _ _)).prodCongr (Equiv.refl Mem)).trans (Equiv.prodAssoc _ _ _)

/-! ## Provers -/

/-- A prover: an operational strategy with arbitrary finite memories whose turn `j` acts on
message register `j`. -/
abbrev Prover (d : Desc) := OpStrategy (Reg d) (Reg d) d.numMsgs

/-- Prover turn `j` on the global system: `act j` on register `j` and the memory, the identity
elsewhere. -/
noncomputable def proverStep {d : Desc} (P : Prover d) (j : ℕ) :
    MatMap (Qubits d.totalWires × P.M j) (Qubits d.totalWires × P.M (j + 1)) :=
  reindexMap (turnSplit d j (P.M (j + 1))).symm ∘ₗ liftR (Rest d j) (P.act j) ∘ₗ
    reindexMap (turnSplit d j (P.M j))

theorem isChannel_proverStep {d : Desc} (P : Prover d) {j : ℕ} (hj : j < d.numMsgs) :
    IsChannel (proverStep P j) :=
  ((isChannel_reindexMap _).comp (P.act_channel j hj).liftR).comp (isChannel_reindexMap _)

/-- **No-signalling for the prover**: a turn leaves the marginal on every wire outside the
message register unchanged — in particular on every private wire. -/
theorem proverStep_marginal {d : Desc} (P : Prover d) {j : ℕ} (hj : j < d.numMsgs)
    (X : Matrix (Qubits d.totalWires × P.M j) (Qubits d.totalWires × P.M j) ℂ) :
    traceRight (Matrix.reindex (turnSplit d j (P.M (j + 1))) (turnSplit d j (P.M (j + 1)))
        (proverStep P j X)) =
      traceRight (Matrix.reindex (turnSplit d j (P.M j)) (turnSplit d j (P.M j)) X) := by
  have e : Matrix.reindex (turnSplit d j (P.M (j + 1))) (turnSplit d j (P.M (j + 1)))
      (proverStep P j X) =
      liftR (Rest d j) (P.act j) (Matrix.reindex (turnSplit d j (P.M j)) (turnSplit d j (P.M j)) X) := by
    simp only [proverStep, LinearMap.comp_apply, reindexMap_apply]
    exact (Matrix.reindex _ _).apply_symm_apply _
  rw [e, traceRight_liftR (P.act_channel j hj).tp]

/-! ## The verifier -/

/-- The unitary of verifier block `j` (gates outside the wire range are dropped; for valid
descriptions none are, see `QIP.ValidGates`). -/
noncomputable def blockMat (d : Desc) (j : ℕ) : Matrix (Qubits d.totalWires) (Qubits d.totalWires) ℂ :=
  layerMat ((d.blocks.getD j []).filterMap (Gate.toInstr? d.totalWires))

theorem blockMat_mem_unitaryGroup (d : Desc) (j : ℕ) :
    blockMat d j ∈ Matrix.unitaryGroup (Qubits d.totalWires) ℂ :=
  layerMat_mem_unitaryGroup _

/-- Verifier block `j` on the global system. -/
noncomputable def verifierStep (d : Desc) (Mem : Type) [Fintype Mem] [DecidableEq Mem] (j : ℕ) :
    MatMap (Qubits d.totalWires × Mem) (Qubits d.totalWires × Mem) :=
  conjMap (blockMat d j ⊗ₖ (1 : Matrix Mem Mem ℂ))

theorem isChannel_verifierStep (d : Desc) (Mem : Type) [Fintype Mem] [DecidableEq Mem] (j : ℕ) :
    IsChannel (verifierStep d Mem j) :=
  isChannel_unitary (kronecker_mem_unitary (blockMat_mem_unitaryGroup d j) (one_mem _))

/-! ## Execution -/

/-- The all-zero basis vector on the verifier wires. -/
def zeroVec (W : ℕ) : Qubits W → ℂ := fun y => if y = Qubits.zero W then 1 else 0

theorem isDensity_zeroVec (W : ℕ) : IsDensity (pureState (zeroVec W)) := by
  rw [isDensity_pure_iff]
  simp [zeroVec, apply_ite]

variable {d : Desc}

/-- The initial global state `|0…0⟩⟨0…0| ⊗ init`. -/
noncomputable def initState (P : Prover d) : Matrix (Qubits d.totalWires × P.M 0)
    (Qubits d.totalWires × P.M 0) ℂ :=
  pureState (zeroVec d.totalWires) ⊗ₖ P.init

/-- The state just after verifier block `j`. -/
noncomputable def stateAfterBlock (P : Prover d) :
    ∀ j, Matrix (Qubits d.totalWires × P.M j) (Qubits d.totalWires × P.M j) ℂ
  | 0 => verifierStep d (P.M 0) 0 (initState P)
  | j + 1 => verifierStep d (P.M (j + 1)) (j + 1) (proverStep P j (stateAfterBlock P j))

/-- The final state, after block `m`. -/
noncomputable def finalState (P : Prover d) :
    Matrix (Qubits d.totalWires × P.M d.numMsgs) (Qubits d.totalWires × P.M d.numMsgs) ℂ :=
  stateAfterBlock P d.numMsgs

/-- The output wire reads `1`. -/
def outBit (d : Desc) (y : Qubits d.totalWires) : Prop :=
  ∃ h : d.out < d.totalWires, y ⟨d.out, h⟩ = true

instance (d : Desc) : DecidablePred (outBit d) := fun y => by unfold outBit; infer_instance

/-- The accepting effect: the output wire reads `1`; the prover memory is ignored. -/
noncomputable def acceptEffect (d : Desc) (Mem : Type) [Fintype Mem] [DecidableEq Mem] :
    Matrix (Qubits d.totalWires × Mem) (Qubits d.totalWires × Mem) ℂ :=
  basisEffect (outBit d) ⊗ₖ (1 : Matrix Mem Mem ℂ)

/-- The probability that the verifier accepts when interacting with `P`. -/
noncomputable def accept (P : Prover d) : ℝ := prob (acceptEffect d (P.M d.numMsgs)) (finalState P)

theorem isDensity_initState (P : Prover d) : IsDensity (initState P) :=
  (isDensity_zeroVec _).kronecker P.init_density

theorem isDensity_stateAfterBlock (P : Prover d) : ∀ j ≤ d.numMsgs, IsDensity (stateAfterBlock P j)
  | 0, _ => (isChannel_verifierStep d _ 0).map_density (isDensity_initState P)
  | j + 1, hj => (isChannel_verifierStep d _ (j + 1)).map_density
      ((isChannel_proverStep P (by omega)).map_density (isDensity_stateAfterBlock P j (by omega)))

theorem final_isDensity (P : Prover d) : IsDensity (finalState P) :=
  isDensity_stateAfterBlock P _ le_rfl

theorem isEffect_kronecker_one {α Mem : Type} [Fintype α] [DecidableEq α] [Fintype Mem]
    [DecidableEq Mem] {E : Matrix α α ℂ} (hE : IsEffect E) :
    IsEffect (E ⊗ₖ (1 : Matrix Mem Mem ℂ)) := by
  constructor
  · exact (hE.posSemidef.kronecker PosSemidef.one).nonneg
  · rw [Matrix.le_iff, ← one_kronecker_one, ← sub_kronecker']
    exact (Matrix.le_iff.mp hE.le_one).kronecker PosSemidef.one

theorem isEffect_acceptEffect (d : Desc) (Mem : Type) [Fintype Mem] [DecidableEq Mem] :
    IsEffect (acceptEffect d Mem) :=
  isEffect_kronecker_one (isEffect_basisEffect _)

/-- **Acceptance probabilities lie in `[0, 1]`.** -/
theorem accept_mem_Icc (P : Prover d) : accept P ∈ Set.Icc 0 1 :=
  prob_mem_Icc (isEffect_acceptEffect d _) (final_isDensity P)

end ShiQIP
