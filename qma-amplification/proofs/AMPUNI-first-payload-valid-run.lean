import «AMPUNI-first-payload-machine»
import «AMPUNI-retained-layer-copy-pass»
import «AMPUNI-payload-copy-valid-run»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMFirstPayload
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMPieceSchedule
abbrev core (k : Fin 14) : TopK := .inl (.inl k)

/-- The first copy uses the local copy-0 layout, consumes only the circuit
payload, and restores the register conditions required by the replay suffix. -/
theorem valid_first_run
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k))
    (hsource : V ShiTMReplayReload.source =
      (ShiTMCircuitNormalization.stripCircPrefix (F.circ n)).map bit)
    (hscratch : V ShiTMReplayReload.scratch = [])
    (hmarks : V ShiTMReplayMarkSplit.marks = [])
    (hret : Retained n (F.wit n) (F.anc n) V)
    (h10 : V (.inl (.inl (10 : Fin 14))) = [])
    (h4 : V (.inl (.inl (4 : Fin 14))) = [Cell.delim])
    (h6 : V (.inl (.inl (6 : Fin 14))) = [])
    (h7 : V (.inl (.inl (7 : Fin 14))) = [])
    (h12 : V (.inl (.inl (12 : Fin 14))) = [])
    (hc0 : V (.inl (.inr (0 : Fin 2))) = List.replicate (F.circ n).length Cell.mark)
    (hc1 : V (.inl (.inr (1 : Fin 2))) = []) :
    ∃ (Q : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some ⟨some (clearLabel .width), none, V⟩) =
        some ⟨some (payloadLabel (some (.inr .exit))), none, Q⟩
      ∧ Q (core 13) = (ShiTMPayloadCopyStage.payloadBytes 0 F n).reverse ++ V (core 13)
      ∧ Q ShiTMReplayReload.source = []
      ∧ Q ShiTMReplayMarkSplit.marks = []
      ∧ Q ShiTMReplayReload.scratch = []
      ∧ Q (core 10) = []
      ∧ Q ShiTMReplayReload.archive = V ShiTMReplayReload.archive
      ∧ Q (core 4) = [Cell.delim]
      ∧ Q (core 6) = [] ∧ Q (core 7) = [] ∧ Q (core 12) = []
      ∧ Q (.inl (.inr (0 : Fin 2))) = []
      ∧ Q (.inl (.inr (1 : Fin 2))) = []
      ∧ Retained n (F.wit n) (F.anc n) Q := by
  obtain ⟨C, hc, hcWidth, hcBase, hc8, hc9, hcf⟩ :=
    ShiTMReplayTableClear.clear_all_run none V
  have hC3 : C (core 3) = [] :=
    (hcf _ (by decide) (by decide) (by decide) (by decide)).trans hscratch
  have hC0 : C (core 0) = [] :=
    (hcf _ (by decide) (by decide) (by decide) (by decide)).trans hmarks
  have hCkeep (j : TopK)
      (h1 : j ≠ core 1) (h2 : j ≠ core 2) (h8 : j ≠ core 8) (h9 : j ≠ core 9) :
      C j = V j := hcf j h1 h2 h8 h9
  have hretC : Retained n (F.wit n) (F.anc n) C := by
    refine ⟨?_, ?_, ?_⟩
    · exact (hCkeep (.inr 0) (by decide) (by decide) (by decide) (by decide)).trans hret.1
    · exact (hCkeep (.inr 1) (by decide) (by decide) (by decide) (by decide)).trans hret.2.1
    · exact (hCkeep (.inr 2) (by decide) (by decide) (by decide) (by decide)).trans hret.2.2
  obtain ⟨T, vt, ht, htables, hretT, hT3, htf⟩ :=
    run_program_finished_frame 0 n (F.wit n) (F.anc n) none C hretC hC3
  let ps := expectedPieces 0 n (F.wit n) (F.anc n)
  have hempty : tableState C = ([], []) := Prod.ext hcWidth hcBase
  have hprogram : runCommands n (F.wit n) (F.anc n) (program 0) ([], []) =
      (pieceCells Prod.fst ps, pieceCells Prod.snd ps) := by
    simpa [ps, expectedPieces] using run_program0 n (F.wit n) (F.anc n) [] []
  rw [hempty, hprogram] at htables
  have hT8 : T (core 8) = [] := (htf _ (by simp [OutsideWrites, core])).trans hc8
  have hT9 : T (core 9) = [] := (htf _ (by simp [OutsideWrites, core])).trans hc9
  have hT10 : T (core 10) = [] :=
    (htf _ (by simp [OutsideWrites, core])).trans
      ((hCkeep _ (by decide) (by decide) (by decide) (by decide)).trans h10)
  obtain ⟨P, hp, hp1, hp2, hp8, hp9, hp10, hpf⟩ :=
    ShiTMMirrorInit.both_run (pieceCells Prod.fst ps) (pieceCells Prod.snd ps) vt T
      (congrArg Prod.fst htables) (congrArg Prod.snd htables) hT8 hT9 hT10
  have hPsrc : P ShiTMReplayReload.source = (ShiTMCircuitNormalization.stripCircPrefix (F.circ n)).map bit :=
    (hpf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((htf _ (by simp [OutsideWrites])).trans
        ((hcf _ (by decide) (by decide) (by decide) (by decide)).trans hsource))
  have hP0 : P (core 0) = [] :=
    (hpf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((htf _ (by simp [OutsideWrites, core])).trans hC0)
  have hP3 : P (core 3) = [] :=
    (hpf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hT3
  have hPa : P ShiTMReplayReload.archive = V ShiTMReplayReload.archive :=
    (hpf _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((htf _ (by simp [OutsideWrites])).trans
        (hcf _ (by decide) (by decide) (by decide) (by decide)))
  have hPret : Retained n (F.wit n) (F.anc n) P := by
    refine ⟨?_, ?_, ?_⟩
    · exact (hpf (.inr 0) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hretT.1
    · exact (hpf (.inr 1) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hretT.2.1
    · exact (hpf (.inr 2) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hretT.2.2
  have hPkeep (j : TopK)
      (h1 : j ≠ core 1) (h2 : j ≠ core 2) (h8 : j ≠ core 8) (h9 : j ≠ core 9)
      (h10 : j ≠ core 10) (hout : OutsideWrites j) : P j = V j :=
    (hpf j h1 h2 h8 h9 h10).trans ((htf j hout).trans (hCkeep j h1 h2 h8 h9))
  have hP4 : P (core 4) = [Cell.delim] :=
    (hPkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [OutsideWrites, core])).trans h4
  have hP6 : P (core 6) = [] :=
    (hPkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [OutsideWrites, core])).trans h6
  have hP7 : P (core 7) = [] :=
    (hPkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [OutsideWrites, core])).trans h7
  have hP12 : P (core 12) = [] :=
    (hPkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [OutsideWrites, core])).trans h12
  have hPc0 : P (.inl (.inr (0 : Fin 2))) = List.replicate (F.circ n).length Cell.mark :=
    (hPkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [OutsideWrites, core])).trans hc0
  have hPc1 : P (.inl (.inr (1 : Fin 2))) = [] :=
    (hPkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [OutsideWrites, core])).trans hc1
  have hP13 : P (core 13) = V (core 13) :=
    hPkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [OutsideWrites, core])
  obtain ⟨Q, bodyCost, hbody, hacc, hQs, hQ0, hQ3, hQ10,
      hQ4, hQ6, hQ7, hQ12, hQc0, hQc1, hQheaders, _⟩ :=
    ShiTMRetainedPayload.layer_copy_pass_from_ready 0 F n P
      hPsrc hP0 hp1 hp2 hP3 hP4 hP6 hP7 hp8 hp9 hp10 hP12 hPc0 hPc1
  have hrun := sequence_run _ _ _ bodyCost
    none none vt none none V C T P Q hc ht hp hbody
  refine ⟨Q, _, hrun, ?_, hQs, hQ0, hQ3, hQ10, ?_,
    hQ4, hQ6, hQ7, hQ12, hQc0, hQc1, ?_⟩
  · exact hacc.trans (congrArg (fun xs => (ShiTMPayloadCopyStage.payloadBytes 0 F n).reverse ++ xs) hP13)
  · exact (hQheaders 3).trans hPa
  · exact ⟨(hQheaders 0).trans hPret.1,
      (hQheaders 1).trans hPret.2.1, (hQheaders 2).trans hPret.2.2⟩

end ShiTMFirstPayload
