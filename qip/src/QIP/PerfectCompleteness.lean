/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Valid

/-!
# Q27 — perfect completeness

`perfDesc d := bellDesc (rejectDesc d)`: the reject-flag description (Q26), followed by the Bell
test (`QIP.Bell.*`). For a valid `d` with the standard `k`-message schedule (`k ≥ 1`):

* **`perfDesc_valid`**, **`hasSchedule_perfDesc`**: `perfDesc d` is valid and has the standard
  `(k + 2)`-message schedule;
* **`perfDesc_complete`**: if `value d ≥ 1/2`, some prover is accepted with certainty;
* **`perfDesc_sound`**: if `value d ≤ 1/3`, then `value (perfDesc d) ≤ 35/36`;
* resources: `numMsgs_perfDesc`, `totalWires_perfDesc`.

Completeness: Q26 gives a prover accepted with probability exactly `1/2`; it is made isometric
(Q17) and clean (`QIP.Clean`), and then answers the Bell test (`exists_iso_accept_one`).
Soundness: `value_bellDesc_le`, with `value (rejectDesc d) = value d`.
-/

namespace ShiQIP

/-- The perfect-completeness transformation. -/
def perfDesc (d : Desc) : Desc := bellDesc (rejectDesc d)

variable {d : Desc} {k : ℕ} (hd : d.Valid) (hs : d.HasSchedule k) (hk : 1 ≤ k)

include hs hk in
theorem one_le_numMsgs_of_hasSchedule : 1 ≤ d.numMsgs := by
  rw [Desc.numMsgs_of_hasSchedule hs]; exact hk

include hs hk in
theorem hasSchedule_rejectDesc : (rejectDesc d).HasSchedule k := by
  unfold Desc.HasSchedule
  rw [schedule_rejectDesc (one_le_numMsgs_of_hasSchedule hs hk)]
  exact hs

include hd hs hk in
theorem rejectDesc_valid_of_hasSchedule : (rejectDesc d).Valid :=
  rejectDesc_valid hd (one_le_numMsgs_of_hasSchedule hs hk) (lastToVerifier_of_hasSchedule hs hk)

include hd hs hk in
/-- **The transformed description is valid.** -/
theorem perfDesc_valid : (perfDesc d).Valid :=
  bellDesc_valid (rejectDesc_valid_of_hasSchedule hd hs hk)
    (lastToVerifier_of_hasSchedule (hasSchedule_rejectDesc hs hk) hk)

include hs hk in
/-- **Two more messages, in the standard schedule.** -/
theorem hasSchedule_perfDesc : (perfDesc d).HasSchedule (k + 2) :=
  hasSchedule_bellDesc (hasSchedule_rejectDesc hs hk)

theorem numMsgs_perfDesc : (perfDesc d).numMsgs = (rejectDesc d).numMsgs + 2 :=
  numMsgs_bellDesc _

theorem totalWires_perfDesc : (perfDesc d).totalWires = 2 * (rejectDesc d).totalWires + 3 :=
  totalWires_bellDesc _

include hd hs hk in
/-- **Perfect completeness.** -/
theorem perfDesc_complete (hv : 1 / 2 ≤ value d) : ∃ P : Prover (perfDesc d), accept P = 1 := by
  have hm := one_le_numMsgs_of_hasSchedule hs hk
  have hlast := lastToVerifier_of_hasSchedule hs hk
  have hd₀ := rejectDesc_valid_of_hasSchedule hd hs hk
  obtain ⟨P, hP⟩ := exists_accept_half hd hm hlast hv
  obtain ⟨T, hT⟩ := exists_isoProver P
  obtain ⟨T', hacc, hclean⟩ := exists_clean T hd₀
  obtain ⟨T'', hT''⟩ := exists_iso_accept_one hd₀ T' hclean (by rw [hacc, hT, hP])
  exact ⟨T''.toOp, hT''⟩

include hd hs hk in
theorem value_perfDesc_eq_one (hv : 1 / 2 ≤ value d) : value (perfDesc d) = 1 := by
  obtain ⟨P, hP⟩ := perfDesc_complete hd hs hk hv
  exact le_antisymm (value_mem_Icc _).2 (hP ▸ accept_le_value _ P)

include hd hs hk in
/-- **Soundness.** -/
theorem perfDesc_sound (hv : value d ≤ 1 / 3) : value (perfDesc d) ≤ 35 / 36 := by
  have hm := one_le_numMsgs_of_hasSchedule hs hk
  have hlast := lastToVerifier_of_hasSchedule hs hk
  refine value_bellDesc_le (rejectDesc_valid_of_hasSchedule hd hs hk) ?_
  rw [value_rejectDesc hd hm hlast]
  exact hv

end ShiQIP
