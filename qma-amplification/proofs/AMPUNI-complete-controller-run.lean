import «AMPUNI-complete-controller-first-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCompleteController

open ShiTMLayoutMachine ShiTMRetainedTop

def firstCopyBytes (F : ShiClassQMA.QMAFamily) (n : Nat) : List Cell :=
  (ShiTMRawLayout.encodeCirc
    (ShiTMRawLayout.mapCirc depth
      (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n)) 0
      ((F.circ n).map (List.map ShiTMRawLayout.ofInstr)))).map bit

def numericBytes (F : ShiClassQMA.QMAFamily) (n : Nat) : List Cell :=
  (ShiBQP.encNat (3 * F.wit n) ++
    ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
    ShiBQP.encNat
      (3 * n + 3 * F.wit n + 3 * F.anc n + 3)).map bit

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The complete finite controller, from an ordinary length-aware input, runs
through the archived first pass and both copy-specific later passes to its
done state. Its accumulator is the exact concatenation of the three verified
mapped-copy encodings and the numeric output header, in reverse orientation. -/
theorem full_three_pass_run (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ (R : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some (Turing.initList finiteMachine
          ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit))) =
        some ⟨some (copyLabel
          (ShiTMCopyStageWithSkip.oldLabel ShiTMCopyStage.doneLabel)),
          none, R⟩
      ∧ R (.inl (.inl (13 : Fin 14))) =
          (ShiTMCopyStageWithSkip.copyBytes 2 F n).reverse ++
            (ShiTMCopyStageWithSkip.copyBytes 1 F n).reverse ++
            (firstCopyBytes F n).reverse ++ (numericBytes F n).reverse
      ∧ R ShiTMReplayReload.source = []
      ∧ R ShiTMReplayMarkSplit.marks = []
      ∧ R ShiTMReplayReload.scratch = []
      ∧ R ShiTMReplayReload.archive =
          List.replicate (F.out n : Nat) Cell.mark ++ Cell.mirrorEnd ::
            ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit).reverse := by
  let input := (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit
  obtain ⟨V, firstSteps, hfirst, hVsrc, hVmarks,
    hVscratch, hV10, hVarchive, hV4, hV6, hV7, hV12,
    hVC0, hVC1, hVret, hVacc⟩ :=
    ShiTMReplayPreface.init_then_first_pass F n
  obtain ⟨R, copySteps, hcopy, hRacc, hRsrc,
    hRmarks, hRscratch, hRarchive, _⟩ :=
    ShiTMCopyStageWithSkip.two_copy_run F n V
      hVsrc hVscratch hVmarks hVarchive hVret
      hV10 hV4 hV6 hV7 hV12 hVC0 hVC1
  have hinit :
      some (Turing.initList finiteMachine input) =
        (some (Turing.initList ShiTMReplayPreface.finiteMachine input)).map
          (liftCfg firstLabel) := by rfl
  have hfirstLift := first_run_lift firstSteps
    (some (Turing.initList ShiTMReplayPreface.finiteMachine input))
    (ShiTMReplayPreface.liftEntryCfg
      ⟨some (ShiTMOutputEntry.parserLabel (.inl (.inr .exit))), none, V⟩)
    rfl hfirst
  have hfirst' : run^[firstSteps]
      (some (Turing.initList finiteMachine input)) =
      some ⟨some (firstLabel firstExit), none, V⟩ := by
    change run^[firstSteps]
      ((some (Turing.initList ShiTMReplayPreface.finiteMachine input)).map
        (liftCfg firstLabel)) = _ at hfirstLift
    rw [← hinit] at hfirstLift
    change run^[firstSteps] (some (Turing.initList finiteMachine input)) =
      some ⟨some (firstLabel firstExit), none, V⟩ at hfirstLift
    exact hfirstLift
  have hbridge : run^[1]
      (some ⟨some (firstLabel firstExit), none, V⟩) =
      some ⟨some (copyLabel copy1Entry), none, V⟩ := by
    simpa using first_exit_step none V
  have hcopyLift := copy_run_lift copySteps
    (some ⟨some copy1Entry, none, V⟩)
  have hcopy' : run^[copySteps]
      (some ⟨some (copyLabel copy1Entry), none, V⟩) =
      some ⟨some (copyLabel
        (ShiTMCopyStageWithSkip.oldLabel ShiTMCopyStage.doneLabel)),
        none, R⟩ := by
    rw [show ShiTMCopyStageWithSkip.run^[copySteps]
        (some ⟨some copy1Entry, none, V⟩) =
        some ⟨some (ShiTMCopyStageWithSkip.oldLabel
          ShiTMCopyStage.doneLabel), none, R⟩ from hcopy] at hcopyLift
    simpa [liftCfg] using hcopyLift
  have hprefix := iterTwo run firstSteps 1 _ _ _ hfirst' hbridge
  have hwhole := iterTwo run (firstSteps + 1) copySteps
    _ _ _ hprefix hcopy'
  refine ⟨R, firstSteps + 1 + copySteps,
    hwhole, ?_, hRsrc,
    hRmarks, hRscratch, hRarchive⟩
  rw [hRacc, hVacc]
  simp only [firstCopyBytes, numericBytes, List.append_assoc]

end ShiTMCompleteController
