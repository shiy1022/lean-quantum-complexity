/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Desc
import QIP.Prefix

/-!
# Q27 — the Bell-test description extends the original verifier

`bellPrefix d : PrefixData d (bellDesc d)`: the wires of `d` embed by `bellShift`, message
registers `j < m` correspond, blocks `j < m` are relabelled copies, and block `m` is block `m`
of `d` followed by `G = CNOT(out → B)` and the swaps into message `m`.
-/

namespace ShiQIP

open Matrix ShiQuantum
open scoped ComplexOrder MatrixOrder Kronecker

variable {d : Desc}

theorem bellShift_lt {x : ℕ} (hx : x < d.totalWires) : bellShift d x < (bellDesc d).totalWires := by
  rw [totalWires_bellDesc]; unfold bellShift; split_ifs <;> omega

theorem bellShift_inj {x y : ℕ} (h : bellShift d x = bellShift d y) : x = y := by
  unfold bellShift at h; split_ifs at h <;> omega

variable (d) in
/-- The wire embedding of the Bell-test description. -/
def bellEmb : Fin d.totalWires ↪ Fin (bellDesc d).totalWires :=
  ⟨fun x => ⟨bellShift d x, bellShift_lt x.2⟩, fun x y h =>
    Fin.ext (bellShift_inj (congrArg Fin.val h))⟩

theorem segs_bellDesc : segs (bellDesc d) = (d.priv + 2) :: (d.msgs.map Message.width ++
    [d.totalWires, 1]) := by
  simp [segs, bellDesc]

theorem psum_bell {j : ℕ} (hj : j ≤ d.numMsgs) :
    psum (segs (bellDesc d)) (j + 1) = psum (segs d) (j + 1) + 2 := by
  rw [segs_bellDesc]
  simp only [segs, psum_cons_succ]
  have : psum (d.msgs.map Message.width ++ [d.totalWires, 1]) j =
      psum (d.msgs.map Message.width) j := by
    simp only [psum]
    rw [List.take_append_of_le_length (by simp [Desc.numMsgs] at hj ⊢; omega)]
  rw [this]; ring

theorem getD_bell {j : ℕ} (hj : j < d.numMsgs) :
    (segs (bellDesc d)).getD (j + 1) 0 = (segs d).getD (j + 1) 0 := by
  rw [segs_bellDesc]
  simp only [segs, List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp [Desc.numMsgs] at hj ⊢; omega)]

theorem inReg_bellEmb {j : ℕ} (hj : j < d.numMsgs) (x : Fin d.totalWires) :
    inReg (bellDesc d) j (bellEmb d x) ↔ inReg d j x := by
  unfold inReg
  rw [msgOffset_eq, msgOffset_eq, msgWidth_eq, msgWidth_eq, psum_bell hj.le, getD_bell hj]
  change psum (segs d) (j + 1) + 2 ≤ bellShift d x ∧
    bellShift d x < psum (segs d) (j + 1) + 2 + (segs d).getD (j + 1) 0 ↔ _
  have hp : d.priv ≤ psum (segs d) (j + 1) := by simp [segs]
  unfold bellShift
  split_ifs <;> omega

theorem mem_range_bellEmb {j : ℕ} (hj : j < d.numMsgs) (v : Fin (bellDesc d).totalWires)
    (hv : inReg (bellDesc d) j v) : v ∈ Set.range (bellEmb d) := by
  unfold inReg at hv
  rw [msgOffset_eq, msgWidth_eq, psum_bell hj.le, getD_bell hj] at hv
  have hp : d.priv ≤ psum (segs d) (j + 1) := by simp [segs]
  have hle := psum_add_getD_le (segs d) (j + 1)
  rw [segs_sum] at hle
  refine ⟨⟨(v : ℕ) - 2, by omega⟩, Fin.ext ?_⟩
  change bellShift d ((v : ℕ) - 2) = v
  unfold bellShift
  rw [if_neg (by omega)]
  omega

theorem blocks_bell_getD {j : ℕ} (hj : j < d.numMsgs + 3) :
    (bellDesc d).blocks.getD j [] = bellBlock d j := by
  simp [bellDesc, List.getD_eq_getElem?_getD, hj]

theorem blockMat_bell_lt (hd : d.Valid) {j : ℕ} (hj : j < d.numMsgs) :
    blockMat (bellDesc d) j =
      (blockMat d j ⊗ₖ (1 : Matrix (Outside (bellEmb d) → Bool) (Outside (bellEmb d) → Bool) ℂ)).submatrix
        (embSplit (bellEmb d)) (embSplit (bellEmb d)) := by
  rw [blockMat, blocks_bell_getD (by omega), bellBlock, if_pos hj,
    filterMap_relabel (bellEmb d) (bellShift d) (fun _ => rfl) _ (hd.toInstr?_isSome j),
    layerMat_map]
  rfl

variable (d) in
/-- The extra gates of block `m`: `CNOT(out → B)` and the swaps into message `m`. -/
noncomputable def bellG : Matrix (Qubits (bellDesc d).totalWires) (Qubits (bellDesc d).totalWires) ℂ :=
  layerMat (([Gate.cnot (bellShift d d.out) (bellB d)] ++ swapAll d).filterMap
    (Gate.toInstr? (bellDesc d).totalWires))

theorem blockMat_bell_last (hd : d.Valid) :
    blockMat (bellDesc d) d.numMsgs = bellG d *
      (blockMat d d.numMsgs ⊗ₖ (1 : Matrix (Outside (bellEmb d) → Bool)
        (Outside (bellEmb d) → Bool) ℂ)).submatrix (embSplit (bellEmb d)) (embSplit (bellEmb d)) := by
  rw [blockMat, blocks_bell_getD (by omega), bellBlock, if_neg (lt_irrefl _), if_pos rfl,
    List.append_assoc, List.filterMap_append, layerMat_append,
    filterMap_relabel (bellEmb d) (bellShift d) (fun _ => rfl) _ (hd.toInstr?_isSome _),
    layerMat_map]
  rfl

variable (d) in
/-- **The Bell-test description extends `d`.** -/
noncomputable def bellPrefix (hd : d.Valid) : PrefixData d (bellDesc d) where
  ε := bellEmb d
  le_msgs := by rw [numMsgs_bellDesc]; omega
  reg j hj x := inReg_bellEmb hj x
  reg_range j hj v hv := mem_range_bellEmb hj v hv
  block j hj := blockMat_bell_lt hd hj
  G := bellG d
  block_last := blockMat_bell_last hd

end ShiQIP
