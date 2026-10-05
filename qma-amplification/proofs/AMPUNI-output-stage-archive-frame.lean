import «AMPUNI-output-stage-full-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputStage

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The numeric-output controller and table initializer do not touch retained
stack 3. This makes it safe to hold the archived input underneath the original
output-index marks on that stack. -/
theorem output_stage_preserves_archive (n wit anc : Nat) (v : Sig)
    (S U : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (h3 : S (.inl (.inl (3 : Fin 14))) = [])
    (h1 : S (.inl (.inl (1 : Fin 14))) = [])
    (h2 : S (.inl (.inl (2 : Fin 14))) = [])
    (h8 : S (.inl (.inl (8 : Fin 14))) = [])
    (h9 : S (.inl (.inl (9 : Fin 14))) = [])
    (h10 : S (.inl (.inl (10 : Fin 14))) = [])
    (hrun : run^[outputStageCost n wit anc]
      (some { l := some (outputLabel (.dispatch 0)), var := v, stk := S }) =
        some ⟨some (stageLabel
          (ShiTMStageChain.parserLabel (.inl (.inr .circuitHeader)))),
          none, U⟩) :
    U (.inr (3 : Fin 4)) = S (.inr (3 : Fin 4)) := by
  obtain ⟨T, w, hout, _, hretT, hT3, hTframe⟩ :=
    ShiTMOutputHeader.run_program_finished n wit anc v S hret h3
  let ko := ShiTMOutputHeader.scheduleCost n wit anc ShiTMOutputHeader.program + 1
  have houtLift : run^[ko]
      (some { l := some (outputLabel (.dispatch 0)), var := v, stk := S }) =
        some { l := some (outputLabel .finished), var := w, stk := T } := by
    simpa [ko, liftCfg, outputLabel] using
      (output_run_lift ko
        { l := some (.dispatch 0), var := v, stk := S }
        { l := some .finished, var := w, stk := T }
        (by simp) (by simpa [ko] using hout))
  have hT1 : T (.inl (.inl (1 : Fin 14))) = [] := by
    rw [hTframe _ (by simp [ShiTMOutputHeader.OutsideWrites])]
    exact h1
  have hT2 : T (.inl (.inl (2 : Fin 14))) = [] := by
    rw [hTframe _ (by simp [ShiTMOutputHeader.OutsideWrites])]
    exact h2
  have hT8 : T (.inl (.inl (8 : Fin 14))) = [] := by
    rw [hTframe _ (by simp [ShiTMOutputHeader.OutsideWrites])]
    exact h8
  have hT9 : T (.inl (.inl (9 : Fin 14))) = [] := by
    rw [hTframe _ (by simp [ShiTMOutputHeader.OutsideWrites])]
    exact h9
  have hT10 : T (.inl (.inl (10 : Fin 14))) = [] := by
    rw [hTframe _ (by simp [ShiTMOutputHeader.OutsideWrites])]
    exact h10
  obtain ⟨V, ks, hstage, _, _, _, _, _, _, _, hstageFrame, hks⟩ :=
    ShiTMStageChain.full_stage_run n wit anc w T hretT hT3
      hT1 hT2 hT8 hT9 hT10
  have hstageLift : run^[ks]
      (some { l := some (stageLabel
          (ShiTMStageChain.tailLabel (.dispatch 0 0))), var := w, stk := T }) =
        some ⟨some (stageLabel
          (ShiTMStageChain.parserLabel (.inl (.inr .circuitHeader)))),
          none, V⟩ := by
    simpa [liftCfg, stageLabel] using
      (stage_run_lift ks
        (some ⟨some (ShiTMStageChain.tailLabel (.dispatch 0 0)), w, T⟩)).trans
        (congrArg (Option.map (liftCfg stageLabel)) hstage)
  have hprefix := iterTwo run ko 1 _ _ _ houtLift (output_bridge w T)
  have hall := iterTwo run (ko + 1) ks _ _ _ hprefix hstageLift
  have hall' : run^[outputStageCost n wit anc]
      (some { l := some (outputLabel (.dispatch 0)), var := v, stk := S }) =
        some ⟨some (stageLabel
          (ShiTMStageChain.parserLabel (.inl (.inr .circuitHeader)))),
          none, V⟩ := by
    simpa [outputStageCost, ko, ← hks, Nat.add_assoc] using hall
  have hVU : V = U := by
    have h := hall'.symm.trans hrun
    exact congrArg Cfg.stk (Option.some.inj h)
  rw [← hVU]
  rw [hstageFrame _ (by simp [ShiTMPieceController.OutsideWrites])
      (by simp) (by simp) (by simp),
    hTframe _ (by simp [ShiTMOutputHeader.OutsideWrites])]

end ShiTMOutputStage
