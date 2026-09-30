import «AMPUNI-output-stage-archive-frame»
import «AMPUNI-output-entry-full-run»
import «AMPUNI-output-entry-parser-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMOuterLift

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The four-header entry phase adds output-index marks on top of the retained
archive; the later numeric-output and table stages leave that stack alone. -/
theorem full_entry_archive_frame (F : ShiClassQMA.QMAFamily) (n : Nat)
    (rest : List Cell) (v : Sig) (S U : ∀ j, List (TopGam j))
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
    (h10 : S (.inl (.inl (10 : Fin 14))) = [])
    (hrun : run^[entryCost F n]
      (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
        some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, U⟩) :
    U (.inr (3 : Fin 4)) =
      List.replicate (F.out n : Nat) Cell.mark ++ S (.inr (3 : Fin 4)) := by
  obtain ⟨H, hheader, _, hH0, hH1, hH2, hH3arc, hHframe⟩ :=
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
  obtain ⟨W, hbody, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    ShiTMOutputStage.full_output_stage_run n (F.wit n) (F.anc n)
      (some Cell.delim) H hret hH13 hH3 hH1' hH2' hH8 hH9 hH10
  have hWarc : W (.inr (3 : Fin 4)) = H (.inr (3 : Fin 4)) :=
    ShiTMOutputStage.output_stage_preserves_archive n (F.wit n) (F.anc n)
      (some Cell.delim) H W hret hH3 hH1' hH2' hH8 hH9 hH10 hbody
  have hbodyLift : run^[ShiTMOutputStage.outputStageCost n (F.wit n) (F.anc n)]
      (some { l := some outputEntry, var := some Cell.delim, stk := H }) =
        some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, W⟩ := by
    simpa [outputEntry, liftCfg, bodyLabel, parserLabel] using
      (body_run_lift (ShiTMOutputStage.outputStageCost n (F.wit n) (F.anc n))
        (some ⟨some (ShiTMOutputStage.outputLabel (.dispatch 0)),
          some Cell.delim, H⟩)).trans
        (congrArg (Option.map (liftCfg bodyLabel)) hbody)
  have hall : run^[entryCost F n]
      (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
        some ⟨some (parserLabel (.inl (.inr .circuitHeader))), none, W⟩ := by
    simpa only [entryCost] using
      (iterTwo run
        ((n + 1) + (F.wit n + 1) + (F.anc n + 1) +
          ((F.out n : Nat) + 1))
        (ShiTMOutputStage.outputStageCost n (F.wit n) (F.anc n))
        _ _ _ hheader hbodyLift)
  have hWU : W = U := by
    have h := hall.symm.trans hrun
    exact congrArg Cfg.stk (Option.some.inj h)
  rw [← hWU, hWarc, hH3arc]

end ShiTMOutputEntry
