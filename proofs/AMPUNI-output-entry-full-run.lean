import «AMPUNI-output-entry-family»
import «AMPUNI-output-entry-body-lift»
import «AMPUNI-output-stage-full-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def entryCost (F : ShiClassQMA.QMAFamily) (n : Nat) : Nat :=
  (n + 1) + (F.wit n + 1) + (F.anc n + 1) +
    ((F.out n : Nat) + 1) +
    ShiTMOutputStage.outputStageCost n (F.wit n) (F.anc n)

/-- Length-aware family headers, amplified numeric output, and amplification
tables execute as one finite top-level machine up to the circuit parser. -/
theorem full_entry_run (F : ShiClassQMA.QMAFamily) (n : Nat)
    (rest : List Cell) (v : Sig) (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit ++ rest)
    (hret0 : S (.inr (0 : Fin 4)) = [])
    (hret1 : S (.inr (1 : Fin 4)) = [])
    (hret2 : S (.inr (2 : Fin 4)) = [])
    (h13 : S (.inl (.inl (13 : Fin 14))) = [])
    (h3 : S (.inl (.inl (3 : Fin 14))) = [])
    (h1 : S (.inl (.inl (1 : Fin 14))) = [])
    (h2 : S (.inl (.inl (2 : Fin 14))) = [])
    (h8 : S (.inl (.inl (8 : Fin 14))) = [])
    (h9 : S (.inl (.inl (9 : Fin 14))) = [])
    (h10 : S (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (U : ∀ j, List (TopGam j)),
      run^[entryCost F n]
        (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
          some { l := some (bodyLabel
            (ShiTMOutputStage.stageLabel
              (ShiTMStageChain.parserLabel (.inl (.inr .circuitHeader))))), var := none, stk := U }
      ∧ U (.inl (.inl (11 : Fin 14))) =
          (ShiBQP.encCirc (F.circ n)).map bit ++ rest
      ∧ U (.inl (.inl (13 : Fin 14))) =
          ((ShiBQP.encNat (3 * F.wit n) ++
            ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
            ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3)).map bit).reverse
      ∧ U (.inl (.inl (1 : Fin 14))) =
          pieceCells Prod.fst
            (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n))
      ∧ U (.inl (.inl (2 : Fin 14))) =
          pieceCells Prod.snd
            (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n))
      ∧ Retained n (F.wit n) (F.anc n) U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ U (.inl (.inl (8 : Fin 14))) =
          (pieceCells Prod.fst
            (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n))).reverse ++
            [Cell.mirrorEnd]
      ∧ U (.inl (.inl (9 : Fin 14))) =
          (pieceCells Prod.snd
            (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n))).reverse ++
            [Cell.mirrorEnd]
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ U (.inl (.inl (0 : Fin 14))) = S (.inl (.inl (0 : Fin 14)))
      ∧ U (.inl (.inl (4 : Fin 14))) = S (.inl (.inl (4 : Fin 14)))
      ∧ U (.inl (.inl (6 : Fin 14))) = S (.inl (.inl (6 : Fin 14)))
      ∧ U (.inl (.inl (7 : Fin 14))) = S (.inl (.inl (7 : Fin 14)))
      ∧ U (.inl (.inl (12 : Fin 14))) = S (.inl (.inl (12 : Fin 14)))
      ∧ U (.inl (.inr (0 : Fin 2))) = S (.inl (.inr (0 : Fin 2)))
      ∧ U (.inl (.inr (1 : Fin 2))) = S (.inl (.inr (1 : Fin 2))) := by
  obtain ⟨H, hheader, hH11, hH0, hH1, hH2, _, hHframe⟩ :=
    family_headers_to_output F n rest v S hsrc
  have hret : Retained n (F.wit n) (F.anc n) H := by
    exact ⟨by simpa [hret0] using hH0,
      by simpa [hret1] using hH1,
      by simpa [hret2] using hH2⟩
  have hH13 : H (.inl (.inl (13 : Fin 14))) = [] := by
    rw [hHframe _ (by simp)]
    exact h13
  have hH3 : H (.inl (.inl (3 : Fin 14))) = [] := by
    rw [hHframe _ (by simp)]
    exact h3
  have hH1' : H (.inl (.inl (1 : Fin 14))) = [] := by
    rw [hHframe _ (by simp)]
    exact h1
  have hH2' : H (.inl (.inl (2 : Fin 14))) = [] := by
    rw [hHframe _ (by simp)]
    exact h2
  have hH8 : H (.inl (.inl (8 : Fin 14))) = [] := by
    rw [hHframe _ (by simp)]
    exact h8
  have hH9 : H (.inl (.inl (9 : Fin 14))) = [] := by
    rw [hHframe _ (by simp)]
    exact h9
  have hH10 : H (.inl (.inl (10 : Fin 14))) = [] := by
    rw [hHframe _ (by simp)]
    exact h10
  obtain ⟨U, hbody, hU13, hU1, hU2, hUret, hU3, hU11,
    hU8, hU9, hU10, hU0, hU4, hU6, hU7, hU12, hUC0, hUC1⟩ :=
    ShiTMOutputStage.full_output_stage_run n (F.wit n) (F.anc n)
      (some Cell.delim) H hret hH13 hH3 hH1' hH2' hH8 hH9 hH10
  have hbodyLift : run^[ShiTMOutputStage.outputStageCost n (F.wit n) (F.anc n)]
      (some { l := some outputEntry, var := some Cell.delim, stk := H }) =
        some { l := some (bodyLabel
          (ShiTMOutputStage.stageLabel
            (ShiTMStageChain.parserLabel (.inl (.inr .circuitHeader))))), var := none, stk := U } := by
    simpa [outputEntry, liftCfg, bodyLabel] using
      (body_run_lift (ShiTMOutputStage.outputStageCost n (F.wit n) (F.anc n))
        (some { l := some (ShiTMOutputStage.outputLabel (.dispatch 0)), var := some Cell.delim, stk := H })).trans
        (congrArg (Option.map (liftCfg bodyLabel)) hbody)
  refine ⟨U, ?_, ?_, hU13, hU1, hU2, hUret, hU3,
    hU8, hU9, hU10, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [entryCost] using
      (iterTwo run
        ((n + 1) + (F.wit n + 1) + (F.anc n + 1) +
          ((F.out n : Nat) + 1))
        (ShiTMOutputStage.outputStageCost n (F.wit n) (F.anc n))
        _ _ _ hheader hbodyLift)
  · rw [hU11]
    exact hH11
  · rw [hU0, hHframe _ (by simp)]
  · rw [hU4, hHframe _ (by simp)]
  · rw [hU6, hHframe _ (by simp)]
  · rw [hU7, hHframe _ (by simp)]
  · rw [hU12, hHframe _ (by simp)]
  · rw [hUC0, hHframe _ (by simp)]
  · rw [hUC1, hHframe _ (by simp)]

end ShiTMOutputEntry
