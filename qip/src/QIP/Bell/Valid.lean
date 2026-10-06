/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import QIP.Bell.Honest

/-!
# Q27 — the Bell-test description is valid

**`bellDesc_valid`**: if `d` is valid and its last message goes to the verifier, `bellDesc d` is
valid: the new output is private, directions still alternate, and every gate touches only wires
held during its block (shipped wires are held during block `m`, message `m` is still with the
verifier then, and `O'` has been returned before block `m + 2`). **`hasSchedule_bellDesc`**: the
standard `k`-message schedule becomes the standard `(k + 2)`-message schedule.
-/


namespace ShiQIP

open ShiShallow

variable {d : Desc}

theorem lt_numMsgs_of_inReg {j : ℕ} {x : Fin d.totalWires} (h : inReg d j x) : j < d.numMsgs := by
  by_contra hc
  have : d.msgWidth j = 0 := by
    rw [msgWidth_eq]; simp [segs, List.getD_eq_getElem?_getD, Desc.numMsgs] at hc ⊢
    rw [List.getElem?_eq_none (by omega)]; rfl
  have := h.2; have := h.1; omega

theorem dir_bell_lt {j : ℕ} (hj : j < d.numMsgs) :
    ((bellDesc d).msgs.map Message.dir).getD j .toVerifier =
      (d.msgs.map Message.dir).getD j .toVerifier := by
  rw [schedule_bellDesc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp [Desc.numMsgs] at hj ⊢; omega)]

theorem dir_bell_m : ((bellDesc d).msgs.map Message.dir).getD d.numMsgs .toVerifier = .toProver := by
  rw [schedule_bellDesc]; simp [Desc.numMsgs]

theorem dir_bell_m1 :
    ((bellDesc d).msgs.map Message.dir).getD (d.numMsgs + 1) .toVerifier = .toVerifier := by
  rw [schedule_bellDesc]; simp [Desc.numMsgs]

/-- Held wires of `d` stay held after relabelling. -/
theorem held_bellShift {i w : ℕ} (h : d.held i w = true) :
    (bellDesc d).held i (bellShift d w) = true := by
  have hw := Desc.held_lt h
  have h' : d.held i ((⟨w, hw⟩ : Fin d.totalWires) : ℕ) = true := h
  change (bellDesc d).held i ((bellEmb d ⟨w, hw⟩ : Fin _) : ℕ) = true
  rw [held_iff] at h' ⊢
  rcases h' with h' | ⟨j, hj, hdir⟩
  · left
    change w < d.priv at h'
    change bellShift d w < d.priv + 2
    unfold bellShift; rw [if_pos h']; omega
  · right
    have hjm := lt_numMsgs_of_inReg hj
    exact ⟨j, (inReg_bellEmb hjm _).mpr hj, by rwa [dir_bell_lt hjm]⟩

theorem held_bell_priv {i w : ℕ} (hw : w < d.priv + 2) : (bellDesc d).held i w = true := by
  simp [Desc.held, bellDesc, hw]

theorem held_bell_msg {x : ℕ} (hx : x < d.totalWires) :
    (bellDesc d).held d.numMsgs (bellMsgOff d + x) = true := by
  have hv : bellMsgOff d + x < (bellDesc d).totalWires := by
    rw [totalWires_bellDesc]; unfold bellMsgOff; omega
  change (bellDesc d).held d.numMsgs ((⟨bellMsgOff d + x, hv⟩ : Fin _) : ℕ) = true
  rw [held_iff]
  right
  refine ⟨d.numMsgs, (inReg_bell_m _).mpr (by
    change bellMsgOff d ≤ bellMsgOff d + x ∧ bellMsgOff d + x < bellMsgOff d + d.totalWires
    omega), ?_⟩
  rw [dir_bell_m]; simp [dirOk]

theorem held_bell_O : (bellDesc d).held (d.numMsgs + 2) (bellO d) = true := by
  change (bellDesc d).held (d.numMsgs + 2) ((wO d : Fin _) : ℕ) = true
  rw [held_iff]
  right
  exact ⟨d.numMsgs + 1, (inReg_bell_m1 _).mpr rfl, by rw [dir_bell_m1]; simp [dirOk]⟩

theorem okBool_bellShift {i : ℕ} {g : Gate} (hg : g.okBool (d.held i) = true) :
    (g.relabel (bellShift d)).okBool ((bellDesc d).held i) = true := by
  cases g with
  | cnot a b =>
    simp only [Gate.okBool, Gate.relabel, Bool.and_eq_true, bne_iff_ne] at hg ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hg
    exact ⟨⟨held_bellShift ha, held_bellShift hb⟩, fun e => hab (bellShift_inj e)⟩
  | _ i => exact held_bellShift hg

theorem alternates_append_two {a b : Message} (hab : a.dir ≠ b.dir) :
    ∀ ms : List Message, Desc.alternates ms = true →
      (∀ hne : ms ≠ [], (ms.getLast hne).dir ≠ a.dir) → Desc.alternates (ms ++ [a, b]) = true
  | [], _, _ => by simp [Desc.alternates, hab]
  | [x], _, hl => by
    have := hl (by simp)
    simp only [List.getLast_singleton] at this
    simp [Desc.alternates, hab, this]
  | x :: y :: rest, h, hl => by
    simp only [Desc.alternates, Bool.and_eq_true, bne_iff_ne] at h
    have ih := alternates_append_two hab (y :: rest) h.2 (fun hne => by
      have := hl (by simp)
      rwa [List.getLast_cons (by simp)] at this)
    simp only [List.cons_append, Desc.alternates, Bool.and_eq_true, bne_iff_ne] at ih ⊢
    exact ⟨h.1, ih⟩

theorem getLast_dir_of_last (hlast : LastToVerifier d) (hne : d.msgs ≠ []) :
    (d.msgs.getLast hne).dir = .toVerifier := by
  have hlen : d.msgs.length - 1 < d.msgs.length := by
    have := List.length_pos_of_ne_nil hne; omega
  unfold LastToVerifier at hlast
  simp only [Desc.numMsgs, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hlen, Option.map_some, Option.getD_some] at hlast
  rw [List.getLast_eq_getElem]
  exact hlast

/-- **The Bell-test description is valid.** -/
theorem bellDesc_valid (hd : d.Valid) (hlast : LastToVerifier d) : (bellDesc d).Valid := by
  unfold Desc.Valid Desc.check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by simp [bellDesc], ?_⟩, ?_⟩, ?_⟩
  · refine alternates_append_two (by simp) _ hd.alternates fun hne => ?_
    rw [getLast_dir_of_last hlast hne]; simp
  · simp [bellDesc, Desc.numMsgs]
  · refine blocksOkFrom_of _ 0 fun i g hg => ?_
    rw [zero_add]
    by_cases hi : i < d.numMsgs + 3
    · rw [blocks_bell_getD hi, bellBlock] at hg
      split_ifs at hg with h1 h2 h3
      · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
        exact okBool_bellShift (by simpa using blocksOkFrom_getD _ 0 i hd.blocksOk g₀ hg₀)
      · subst h2
        rw [List.mem_append, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
          exact okBool_bellShift (by simpa using blocksOkFrom_getD _ 0 _ hd.blocksOk g₀ hg₀)
        · have ho := hd.out_lt
          simp only [List.mem_singleton] at hg
          subst hg
          simp only [Gate.okBool, Bool.and_eq_true, bne_iff_ne]
          refine ⟨⟨held_bell_priv ?_, held_bell_priv ?_⟩, ?_⟩
          · unfold bellShift; rw [if_pos ho]; omega
          · unfold bellB; omega
          · unfold bellShift bellB; rw [if_pos ho]; omega
        · obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg
          rw [List.mem_range] at hx
          split_ifs at hgx with hh
          · have h1 := held_bellShift (i := d.numMsgs) hh
            have h2 := held_bell_msg (d := d) hx
            have hne : bellShift d x ≠ bellMsgOff d + x := by
              have := bellShift_lt_msgOff (d := d) hx; omega
            simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at hgx
            rcases hgx with rfl | rfl | rfl <;>
              simp [Gate.okBool, h1, h2, hne, Ne.symm hne]
          · simp at hgx
      · simp at hg
      · have hpw := priv_le_totalWires d
        have hB : (bellDesc d).held i (bellB d) = true := held_bell_priv (by unfold bellB; omega)
        have hOut : (bellDesc d).held i (bellOut d) = true :=
          held_bell_priv (by unfold bellOut; omega)
        have hi2 : i = d.numMsgs + 2 := by omega
        subst hi2
        have hO := held_bell_O (d := d)
        have hOB : bellO d ≠ bellB d := by unfold bellO bellB; omega
        have hOo : bellO d ≠ bellOut d := by unfold bellO bellOut; omega
        have hBo : bellB d ≠ bellOut d := by unfold bellB bellOut; omega
        rw [bellFinal, List.mem_append] at hg
        rcases hg with hg | hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl | rfl <;> simp [Gate.okBool, hO, hB, hOB]
        · exact okBool_toffoliGates hO hB hOut hOB hOo hBo g hg
    · rw [show (bellDesc d).blocks.getD i [] = [] by
        simp [bellDesc, List.getD_eq_getElem?_getD, hi]] at hg
      simp at hg

theorem stdSchedule_add_two (k : ℕ) :
    stdSchedule (k + 2) = stdSchedule k ++ [.toProver, .toVerifier] := by
  unfold stdSchedule
  rw [show k + 2 = (k + 1) + 1 from rfl, List.range_succ, List.range_succ, List.map_append,
    List.map_append, List.append_assoc]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    have : (k + 1 + 1 - 1 - i) % 2 = (k - 1 - i) % 2 := by
      rw [show k + 1 + 1 - 1 - i = (k - 1 - i) + 2 by omega, Nat.add_mod_right]
    rw [this]
  · simp

/-- **The schedule grows by one round.** -/
theorem hasSchedule_bellDesc {k : ℕ} (h : d.HasSchedule k) : (bellDesc d).HasSchedule (k + 2) := by
  unfold Desc.HasSchedule at h ⊢
  rw [schedule_bellDesc, h, stdSchedule_add_two]

end ShiQIP
