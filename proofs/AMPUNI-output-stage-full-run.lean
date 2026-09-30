import «AMPUNI-output-stage-output-lift»
import «AMPUNI-stage-chain-full-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputStage

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def outputStageCost (n wit anc : Nat) : Nat :=
  ShiTMOutputHeader.scheduleCost n wit anc ShiTMOutputHeader.program + 2 +
    ShiTMStageChain.stageCost n wit anc

/-- The output-header controller and table initializer execute in one finite
machine, reaching the circuit parser with a reversed numeric header already
on the accumulator. -/
theorem full_output_stage_run (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (h13 : S (.inl (.inl (13 : Fin 14))) = [])
    (h3 : S (.inl (.inl (3 : Fin 14))) = [])
    (h1 : S (.inl (.inl (1 : Fin 14))) = [])
    (h2 : S (.inl (.inl (2 : Fin 14))) = [])
    (h8 : S (.inl (.inl (8 : Fin 14))) = [])
    (h9 : S (.inl (.inl (9 : Fin 14))) = [])
    (h10 : S (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[outputStageCost n wit anc]
        (some { l := some (outputLabel (.dispatch 0)), var := v, stk := S }) =
          some { l := some (stageLabel
              (ShiTMStageChain.parserLabel (.inl (.inr .circuitHeader)))), var := none, stk := U }
      ∧ U (.inl (.inl (13 : Fin 14))) =
          ((ShiBQP.encNat (3 * wit) ++
            ShiBQP.encNat (2 * n + 3 * anc + 3) ++
            ShiBQP.encNat (3 * n + 3 * wit + 3 * anc + 3)).map bit).reverse
      ∧ U (.inl (.inl (1 : Fin 14))) =
          pieceCells Prod.fst
            (ShiTMRawLayout.ampPieces n wit anc)
      ∧ U (.inl (.inl (2 : Fin 14))) =
          pieceCells Prod.snd
            (ShiTMRawLayout.ampPieces n wit anc)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ U (.inl (.inl (11 : Fin 14))) = S (.inl (.inl (11 : Fin 14)))
      ∧ U (.inl (.inl (8 : Fin 14))) =
          (pieceCells Prod.fst (ShiTMRawLayout.ampPieces n wit anc)).reverse ++
            [Cell.mirrorEnd]
      ∧ U (.inl (.inl (9 : Fin 14))) =
          (pieceCells Prod.snd (ShiTMRawLayout.ampPieces n wit anc)).reverse ++
            [Cell.mirrorEnd]
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ U (.inl (.inl (0 : Fin 14))) = S (.inl (.inl (0 : Fin 14)))
      ∧ U (.inl (.inl (4 : Fin 14))) = S (.inl (.inl (4 : Fin 14)))
      ∧ U (.inl (.inl (6 : Fin 14))) = S (.inl (.inl (6 : Fin 14)))
      ∧ U (.inl (.inl (7 : Fin 14))) = S (.inl (.inl (7 : Fin 14)))
      ∧ U (.inl (.inl (12 : Fin 14))) = S (.inl (.inl (12 : Fin 14)))
      ∧ U (.inl (.inr (0 : Fin 2))) = S (.inl (.inr (0 : Fin 2)))
      ∧ U (.inl (.inr (1 : Fin 2))) = S (.inl (.inr (1 : Fin 2))) := by
  obtain ⟨T, w, hout, hT13, hretT, hT3, hTframe⟩ :=
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
  obtain ⟨U, ks, hstage, hU1, hU2, hU8, hU9, hU10, hUret, hU3,
    hstageFrame, hks⟩ :=
    ShiTMStageChain.full_stage_run n wit anc w T hretT hT3
      hT1 hT2 hT8 hT9 hT10
  have hstageLift : run^[ks]
      (some { l := some (stageLabel
          (ShiTMStageChain.tailLabel (.dispatch 0 0))), var := w, stk := T }) =
        some { l := some (stageLabel
          (ShiTMStageChain.parserLabel (.inl (.inr .circuitHeader)))), var := none, stk := U } := by
    simpa [liftCfg, stageLabel] using
      (stage_run_lift ks
        (some { l := some (ShiTMStageChain.tailLabel (.dispatch 0 0)), var := w, stk := T })).trans
        (congrArg (Option.map (liftCfg stageLabel)) hstage)
  have hbridge := output_bridge w T
  have hprefix := iterTwo run ko 1 _ _ _ houtLift hbridge
  have hall := iterTwo run (ko + 1) ks _ _ _ hprefix hstageLift
  have hframeAt (j : TopK)
      (hp : ShiTMPieceController.OutsideWrites j)
      (hj8 : j ≠ .inl (.inl (8 : Fin 14)))
      (hj9 : j ≠ .inl (.inl (9 : Fin 14)))
      (hj10 : j ≠ .inl (.inl (10 : Fin 14)))
      (ho : ShiTMOutputHeader.OutsideWrites j) : U j = S j := by
    rw [hstageFrame j hp hj8 hj9 hj10, hTframe j ho]
  refine ⟨U, ?_, ?_, hU1, hU2, hUret, hU3, ?_, hU8, hU9, hU10,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [outputStageCost, ko, ← hks, Nat.add_assoc] using hall
  · have hU13 : U (.inl (.inl (13 : Fin 14))) =
        T (.inl (.inl (13 : Fin 14))) := by
      exact hstageFrame _ (by simp [ShiTMPieceController.OutsideWrites])
        (by simp) (by simp) (by simp)
    rw [hU13, hT13, h13]
    exact ShiTMOutputHeader.program_correct_encoding n wit anc
  · exact hframeAt _ (by simp [ShiTMPieceController.OutsideWrites])
      (by simp) (by simp) (by simp)
      (by simp [ShiTMOutputHeader.OutsideWrites])
  all_goals
    exact hframeAt _ (by simp [ShiTMPieceController.OutsideWrites])
      (by simp) (by simp) (by simp)
      (by simp [ShiTMOutputHeader.OutsideWrites])

end ShiTMOutputStage
