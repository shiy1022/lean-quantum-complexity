/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.CircuitSemantics
import QIP.Resources
import Quantum.ChannelTensor

/-!
# Q15 — operational interaction

The interaction of a verifier description `d : Desc` (`QIP.Syntax`) with a prover.

**Global system.** The `W = d.totalWires` verifier wires (`Qubits W`), followed by the prover's
private memory `Mem`, an **arbitrary** finite type chosen by the prover. Initially every wire is
`|0⟩` and the memory is in a prover-chosen density operator `init`, uncorrelated with the wires
(`initState`). Message registers that the prover owns start at `|0⟩`; the prover may overwrite
them on its turn, so this loses no generality.

**Schedule.** For `j = 0, …, m` (`m = d.numMsgs`): verifier block `j` acts, then, if `j < m`,
prover turn `j` acts. Message `j` is transferred during turn `j`. Finally the output wire is
measured (`accept`).

**Ownership.** During turn `j` the prover owns exactly the wires of the message registers `k`
with `k` prover → verifier and `j ≤ k` (prepared by the prover, not yet sent) or `k` verifier →
prover and `k ≤ j` (already received), together with its memory (`Desc.proverOwns`). It never
owns a private wire (`proverOwns_private`). A **legal** prover action at turn `j` is
`id ⊗ Ψ` for an arbitrary channel `Ψ` on (owned wires × memory) after splitting the wires
(`legalAction`). It therefore cannot change the marginal of the wires it does not own
(`legalAction_marginal`), in particular of verifier-private wires.

**Verifier.** Block `j` is the unitary `layerMat` of its gates (`Gate.toInstr?` to
`ShiShallow.Instr`, then `QIP.GateMatrix`), tensored with the identity on the prover memory.
Ownership of the verifier's gates is enforced by `Desc.Valid` in the class definitions.

* `final_isDensity`: the final state is a density operator;
* `accept_mem_Icc`: the acceptance probability lies in `[0, 1]`.

No bound is placed on the prover's circuit complexity or memory dimension.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## Prover ownership -/

/-- Whether wire `w` lies in a message register owned by the prover at turn `j`, scanning
messages from index `k`, whose register starts at wire `off`. -/
def msgProverOwned (j w : ℕ) : List Message → ℕ → ℕ → Bool
  | [], _, _ => false
  | m :: ms, k, off =>
    (decide (off ≤ w ∧ w < off + m.width) &&
        (match m.dir with
          | .toVerifier => decide (j ≤ k)
          | .toProver => decide (k ≤ j))) ||
      msgProverOwned j w ms (k + 1) (off + m.width)

theorem msgProverOwned_ge {j w : ℕ} :
    ∀ (ms : List Message) (k off : ℕ), msgProverOwned j w ms k off = true → off ≤ w
  | [], _, _, h => by simp [msgProverOwned] at h
  | m :: ms, k, off, h => by
    simp only [msgProverOwned, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hw, _⟩, _⟩ | h
    · exact hw
    · have := msgProverOwned_ge ms (k + 1) (off + m.width) h; omega

/-- Whether the prover owns wire `w` during turn `j`. -/
def Desc.proverOwns (d : Desc) (j w : ℕ) : Bool := msgProverOwned j w d.msgs 0 d.priv

/-- **The prover never owns a private wire.** -/
theorem proverOwns_private {d : Desc} {j w : ℕ} (hw : w < d.priv) : d.proverOwns j w = false := by
  cases h : d.proverOwns j w
  · rfl
  · have := msgProverOwned_ge _ _ _ h; omega

/-! ## Splitting the wires at a prover turn -/

section Split

variable (d : Desc) (j : ℕ)

/-- The predicate "owned by the prover at turn `j`" on wires. -/
def ownPred : Fin d.totalWires → Prop := fun w => d.proverOwns j w = true

instance : DecidablePred (ownPred d j) := fun _ => inferInstanceAs (Decidable (_ = true))

/-- Basis of the prover-owned wires at turn `j`. -/
abbrev OwnP := {w : Fin d.totalWires // ownPred d j w} → Bool

/-- Basis of the wires not owned by the prover at turn `j` (all private wires among them). -/
abbrev VerP := {w : Fin d.totalWires // ¬ ownPred d j w} → Bool

/-- `Qubits W ≃ VerP × OwnP` (verifier side on the left). -/
def wireSplit : Qubits d.totalWires ≃ VerP d j × OwnP d j :=
  (Equiv.piEquivPiSubtypeProd (ownPred d j) (fun _ => Bool)).trans (Equiv.prodComm _ _)

/-- `Qubits W × Mem ≃ VerP × (OwnP × Mem)`. -/
def globalSplit (Mem : Type) : Qubits d.totalWires × Mem ≃ VerP d j × (OwnP d j × Mem) :=
  ((wireSplit d j).prodCongr (Equiv.refl Mem)).trans (Equiv.prodAssoc _ _ _)

/-- A legal prover action at turn `j`: an arbitrary map `Ψ` on (owned wires × memory), and the
identity on every other wire. -/
def legalAction {Mem : Type} (Ψ : MatMap (OwnP d j × Mem) (OwnP d j × Mem)) :
    MatMap (Qubits d.totalWires × Mem) (Qubits d.totalWires × Mem) :=
  reindexMap (globalSplit d j Mem).symm ∘ₗ liftR (VerP d j) Ψ ∘ₗ reindexMap (globalSplit d j Mem)

theorem isChannel_legalAction {Mem : Type} [Fintype Mem] [DecidableEq Mem]
    {Ψ : MatMap (OwnP d j × Mem) (OwnP d j × Mem)} (h : IsChannel Ψ) :
    IsChannel (legalAction d j Ψ) :=
  ((isChannel_reindexMap _).comp h.liftR).comp (isChannel_reindexMap _)

/-- **No-signalling for the prover**: a legal action leaves the marginal on every wire the
prover does not own unchanged. -/
theorem legalAction_marginal {Mem : Type} [Fintype Mem] {Ψ : MatMap (OwnP d j × Mem)
    (OwnP d j × Mem)} (h : IsTP Ψ) (X : Matrix (Qubits d.totalWires × Mem)
    (Qubits d.totalWires × Mem) ℂ) :
    traceRight (Matrix.reindex (globalSplit d j Mem) (globalSplit d j Mem) (legalAction d j Ψ X)) =
      traceRight (Matrix.reindex (globalSplit d j Mem) (globalSplit d j Mem) X) := by
  have e : Matrix.reindex (globalSplit d j Mem) (globalSplit d j Mem) (legalAction d j Ψ X) =
      liftR (VerP d j) Ψ (Matrix.reindex (globalSplit d j Mem) (globalSplit d j Mem) X) := by
    simp only [legalAction, LinearMap.comp_apply, reindexMap_apply]
    exact (Matrix.reindex _ _).apply_symm_apply _
  rw [e, traceRight_liftR h]

end Split

/-! ## Provers -/

/-- A prover for `d`: an arbitrary finite private memory, an initial density operator on it,
and one channel per turn acting on the wires it owns at that turn together with its memory. -/
structure Prover (d : Desc) where
  Mem : Type
  [memFintype : Fintype Mem]
  [memDecEq : DecidableEq Mem]
  init : Matrix Mem Mem ℂ
  init_density : IsDensity init
  act : ∀ j : Fin d.numMsgs, MatMap (OwnP d j × Mem) (OwnP d j × Mem)
  act_channel : ∀ j, IsChannel (act j)

attribute [instance] Prover.memFintype Prover.memDecEq

/-! ## The verifier -/

/-- The unitary of verifier block `j` (gates outside the wire range are dropped; valid
descriptions have none). -/
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
noncomputable def initState (P : Prover d) : Matrix (Qubits d.totalWires × P.Mem)
    (Qubits d.totalWires × P.Mem) ℂ :=
  pureState (zeroVec d.totalWires) ⊗ₖ P.init

/-- The prover's turn `j` on the global system (the identity for `j ≥ m`). -/
noncomputable def proverStep (P : Prover d) (j : ℕ) :
    MatMap (Qubits d.totalWires × P.Mem) (Qubits d.totalWires × P.Mem) :=
  if h : j < d.numMsgs then legalAction d j (P.act ⟨j, h⟩) else LinearMap.id

theorem isChannel_proverStep (P : Prover d) (j : ℕ) : IsChannel (proverStep P j) := by
  unfold proverStep
  split_ifs with h
  · exact isChannel_legalAction d j (P.act_channel _)
  · exact isChannel_id

/-- The state just after verifier block `j`. -/
noncomputable def stateAfterBlock (P : Prover d) :
    ℕ → Matrix (Qubits d.totalWires × P.Mem) (Qubits d.totalWires × P.Mem) ℂ
  | 0 => verifierStep d P.Mem 0 (initState P)
  | j + 1 => verifierStep d P.Mem (j + 1) (proverStep P j (stateAfterBlock P j))

/-- The final state, after block `m`. -/
noncomputable def finalState (P : Prover d) :
    Matrix (Qubits d.totalWires × P.Mem) (Qubits d.totalWires × P.Mem) ℂ :=
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
noncomputable def accept (P : Prover d) : ℝ := prob (acceptEffect d P.Mem) (finalState P)

theorem isDensity_initState (P : Prover d) : IsDensity (initState P) :=
  (isDensity_zeroVec _).kronecker P.init_density

theorem isDensity_stateAfterBlock (P : Prover d) : ∀ j, IsDensity (stateAfterBlock P j)
  | 0 => (isChannel_verifierStep d P.Mem 0).map_density (isDensity_initState P)
  | j + 1 => (isChannel_verifierStep d P.Mem (j + 1)).map_density
      ((isChannel_proverStep P j).map_density (isDensity_stateAfterBlock P j))

theorem final_isDensity (P : Prover d) : IsDensity (finalState P) :=
  isDensity_stateAfterBlock P _

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
  prob_mem_Icc (isEffect_acceptEffect d P.Mem) (final_isDensity P)

end ShiQIP
