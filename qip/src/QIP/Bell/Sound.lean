/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Run
import QIP.Purified

/-!
# Q27 — soundness of the Bell test

**`accept_bell_le`**: against any isometric prover, `bellDesc d` accepts with probability at
most `1/2 + √(p(1-p))`, where `p` is the acceptance probability of the restricted prover in `d`.
Hence **`value_bellDesc_le`**: if `value d ≤ 1/3` then `value (bellDesc d) ≤ 35/36`.
-/


namespace ShiQIP

open Matrix ShiQuantum ShiShallow
open scoped ComplexOrder MatrixOrder Kronecker

variable {d : Desc}

theorem blockMat_bell_mid : blockMat (bellDesc d) (d.numMsgs + 1) = 1 := by
  rw [blockMat, blocks_bell_getD (by omega), bellBlock, if_neg (by omega), if_neg (by omega),
    if_pos rfl]
  rfl

theorem not_inReg_wB (j : ℕ) : ¬ inReg (bellDesc d) j (wB d) :=
  not_inReg_of_lt_priv _ j _ (by change bellB d < d.priv + 2; unfold bellB; omega)

theorem not_inReg_wOut (j : ℕ) : ¬ inReg (bellDesc d) j (wOut d) :=
  not_inReg_of_lt_priv _ j _ (by change bellOut d < d.priv + 2; unfold bellOut; omega)

theorem outBit_iff (y : Qubits d.totalWires) (h : d.out < d.totalWires) :
    outBit d y ↔ y ⟨d.out, h⟩ = true :=
  ⟨fun ⟨_, e⟩ => e, fun e => ⟨h, e⟩⟩

variable (hd : d.Valid)
  (T : IsoStrategy (Reg (bellDesc d)) (Reg (bellDesc d)) (bellDesc d).numMsgs)

include hd in
/-- `pBell` is the acceptance probability of the restricted prover. -/
theorem accept_restrict : accept ((bellPrefix d hd).restrict T).toOp = pBell d hd T := by
  rw [accept_pureRun, accept_expect, pBell]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun μ _ => ?_
  by_cases h : y ⟨d.out, out_lt_W hd⟩ = true
  · rw [if_pos ((outBit_iff y (out_lt_W hd)).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((outBit_iff y (out_lt_W hd)).mp h')), if_neg h]

include hd in
/-- **Bell-test soundness against an isometric prover.** -/
theorem accept_bell_le : accept T.toOp ≤ 1 / 2 + Real.sqrt (pBell d hd T * (1 - pBell d hd T)) := by
  have hacc : accept T.toOp = (star (pureRun T (d.numMsgs + 2)) ⬝ᵥ
      (acceptEffect (bellDesc d) (T.M (d.numMsgs + 2)) *ᵥ pureRun T (d.numMsgs + 2))).re := by
    have key : ∀ k, k = (bellDesc d).numMsgs → accept T.toOp = (star (pureRun T k) ⬝ᵥ
        (acceptEffect (bellDesc d) (T.M k) *ᵥ pureRun T k)).re := by
      intro k hk; subst hk; exact accept_pureRun T
    exact key _ (numMsgs_bellDesc d).symm
  have hm2 : d.numMsgs + 1 < (bellDesc d).numMsgs := by rw [numMsgs_bellDesc]; omega
  have hm1 : d.numMsgs < (bellDesc d).numMsgs := by rw [numMsgs_bellDesc]; omega
  set ψ1 := pureRun T (d.numMsgs + 1) with hψ1def
  set ξ := turnVec T (d.numMsgs + 1) ψ1 with hξdef
  have hrun : ∀ y μ, pureRun T (d.numMsgs + 2) (y, μ) =
      runLayer (finalInstrs d) (fun y' => ξ (y', μ)) y := by
    intro y μ
    change ((blockMat (bellDesc d) (d.numMsgs + 2) ⊗ₖ (1 : Matrix (T.M (d.numMsgs + 2))
      (T.M (d.numMsgs + 2)) ℂ)) *ᵥ ξ) (y, μ) = _
    rw [kron_one_mulVec_apply, blockMat_bell_final, layerMat_mulVec]
  have hψ1 : ψ1 = turnVec T d.numMsgs (pureRun T d.numMsgs) := by
    change (blockMat (bellDesc d) (d.numMsgs + 1) ⊗ₖ (1 : Matrix (T.M (d.numMsgs + 1))
      (T.M (d.numMsgs + 1)) ℂ)) *ᵥ _ = _
    rw [blockMat_bell_mid, one_kronecker_one, one_mulVec]
  have hclean1 : ∀ y μ, y (wOut d) = true → ψ1 (y, μ) = 0 := by
    rw [hψ1]
    exact turnVec_vanish T _ (wOut d) (not_inReg_wOut _) _
      (fun y μ h => pureRun_bell_wOut hd T y μ h)
  have hξ : ∀ y μ, y (wOut d) = true → ξ (y, μ) = 0 :=
    turnVec_vanish T _ (wOut d) (not_inReg_wOut _) ψ1 hclean1
  have hmarg : margB (wB d) ξ = margB (wB d) (pureRun T d.numMsgs) := by
    rw [hξdef, margB_turnVec T hm2 (wB d) (not_inReg_wB _), hψ1,
      margB_turnVec T hm1 (wB d) (not_inReg_wB _)]
  have hp := accept_mem_Icc ((bellPrefix d hd).restrict T).toOp
  rw [accept_restrict hd T] at hp
  rw [hacc, accept_expect_bell]
  simp only [hrun]
  rw [acceptSum_final ξ hξ]
  refine (bellPr_le _ _ (Ne.symm wO_ne_wB) ξ).trans (le_of_eq ?_)
  rw [hmarg, margB_bell hd T]
  exact fidelity_diag_half_sq hp.1 hp.2

include hd in
/-- **Bell-test soundness.** If `value d ≤ 1/3`, then `value (bellDesc d) ≤ 35/36`. -/
theorem value_bellDesc_le (hv : value d ≤ 1 / 3) : value (bellDesc d) ≤ 35 / 36 := by
  obtain ⟨P, hP⟩ := value_attained (bellDesc d)
  obtain ⟨T, hT⟩ := exists_isoProver P
  rw [← hP, ← hT]
  have hp := accept_mem_Icc ((bellPrefix d hd).restrict T).toOp
  have hpv := accept_le_value d ((bellPrefix d hd).restrict T).toOp
  rw [accept_restrict hd T] at hp hpv
  calc accept T.toOp ≤ 1 / 2 + Real.sqrt (pBell d hd T * (1 - pBell d hd T)) :=
        accept_bell_le hd T
    _ ≤ 1 - (1 / 2 - pBell d hd T) ^ 2 := half_add_sqrt_le hp.1 hp.2
    _ ≤ 35 / 36 := bell_bound_third (hpv.trans hv)

end ShiQIP
