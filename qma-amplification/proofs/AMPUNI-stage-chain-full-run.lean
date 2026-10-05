import «AMPUNI-stage-chain-component-lift»
import «AMPUNI-piece-full-program»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMStageChain

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule
open ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def stageCost (n wit anc : Nat) : Nat :=
  scheduleCost n wit anc tailProgram +
    scheduleCost n wit anc (program 2) +
    scheduleCost n wit anc (program 1) +
    scheduleCost n wit anc (program 0) +
    2 * (pieceCells Prod.fst (ShiTMRawLayout.ampPieces n wit anc)).length +
    2 * (pieceCells Prod.snd (ShiTMRawLayout.ampPieces n wit anc)).length + 15

/-- From retained unary fields and empty table/mirror stacks, the one finite
machine runs the tail, copies 2/1/0, and mirror initializer in order, reaching
the nested circuit parser with the exact amplification tables. -/
theorem full_stage_run (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (h3 : S (.inl (.inl (3 : Fin 14))) = [])
    (h1 : S (.inl (.inl (1 : Fin 14))) = [])
    (h2 : S (.inl (.inl (2 : Fin 14))) = [])
    (h8 : S (.inl (.inl (8 : Fin 14))) = [])
    (h9 : S (.inl (.inl (9 : Fin 14))) = [])
    (h10 : S (.inl (.inl (10 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (steps : Nat),
      run^[steps]
        (some { l := some (tailLabel (.dispatch 0 0)), var := v, stk := S }) =
          some { l := some (parserLabel (.inl (.inr .circuitHeader))), var := none, stk := U }
      ∧ U (.inl (.inl (1 : Fin 14))) =
          pieceCells Prod.fst (ShiTMRawLayout.ampPieces n wit anc)
      ∧ U (.inl (.inl (2 : Fin 14))) =
          pieceCells Prod.snd (ShiTMRawLayout.ampPieces n wit anc)
      ∧ U (.inl (.inl (8 : Fin 14))) =
          (pieceCells Prod.fst (ShiTMRawLayout.ampPieces n wit anc)).reverse ++
            [Cell.mirrorEnd]
      ∧ U (.inl (.inl (9 : Fin 14))) =
          (pieceCells Prod.snd (ShiTMRawLayout.ampPieces n wit anc)).reverse ++
            [Cell.mirrorEnd]
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ (∀ j, OutsideWrites j →
          j ≠ .inl (.inl (8 : Fin 14)) →
          j ≠ .inl (.inl (9 : Fin 14)) →
          j ≠ .inl (.inl (10 : Fin 14)) → U j = S j)
      ∧ steps = stageCost n wit anc := by
  let ps := ShiTMRawLayout.ampPieces n wit anc
  let widths := pieceCells Prod.fst ps
  let bases := pieceCells Prod.snd ps
  let kt := scheduleCost n wit anc tailProgram + 1
  let k2 := scheduleCost n wit anc (program 2) + 1
  let k1 := scheduleCost n wit anc (program 1) + 1
  let k0 := scheduleCost n wit anc (program 0) + 1
  let km := (2 * widths.length + 3) + (2 * bases.length + 3)
  obtain ⟨T0, w0, htail, htable0, hret0, hscratch0, hframe0⟩ :=
    ShiTMPieceParam.tail_program_finished n wit anc v S hret h3 h1 h2
  have htailLift : run^[kt]
      (some { l := some (tailLabel (.dispatch 0 0)), var := v, stk := S }) =
        some { l := some (tailLabel (.finished 0)), var := w0, stk := T0 } := by
    simpa [kt, liftCfg, tailLabel] using
      (tail_run_lift kt
        { l := some (.dispatch 0 0), var := v, stk := S }
        { l := some (.finished 0), var := w0, stk := T0 }
        (by simp) (by simpa [kt] using htail))
  have hT0 : tableState T0 = runCommands n wit anc tailProgram ([], []) := by
    exact htable0.trans (by simpa using (run_tailProgram n wit anc [] []).symm)
  obtain ⟨T2, w2, hcopy2, htable2, hret2, hscratch2, hframe2⟩ :=
    run_program_finished_frame 2 n wit anc w0 T0 hret0 hscratch0
  have hcopy2Lift : run^[k2]
      (some { l := some (copyLabel (.dispatch 2 0)), var := w0, stk := T0 }) =
        some { l := some (copyLabel (.finished 2)), var := w2, stk := T2 } := by
    simpa [k2, liftCfg, copyLabel] using
      (copy_run_lift k2
        { l := some (.dispatch 2 0), var := w0, stk := T0 }
        { l := some (.finished 2), var := w2, stk := T2 }
        (by simp) (by simpa [k2] using hcopy2))
  obtain ⟨T1, w1, hcopy1, htable1, hret1, hscratch1, hframe1⟩ :=
    run_program_finished_frame 1 n wit anc w2 T2 hret2 hscratch2
  have hcopy1Lift : run^[k1]
      (some { l := some (copyLabel (.dispatch 1 0)), var := w2, stk := T2 }) =
        some { l := some (copyLabel (.finished 1)), var := w1, stk := T1 } := by
    simpa [k1, liftCfg, copyLabel] using
      (copy_run_lift k1
        { l := some (.dispatch 1 0), var := w2, stk := T2 }
        { l := some (.finished 1), var := w1, stk := T1 }
        (by simp) (by simpa [k1] using hcopy1))
  obtain ⟨T3, w3, hcopy0, htable3, hret3, hscratch3, hframe3⟩ :=
    run_program_finished_frame 0 n wit anc w1 T1 hret1 hscratch1
  have hcopy0Lift : run^[k0]
      (some { l := some (copyLabel (.dispatch 0 0)), var := w1, stk := T1 }) =
        some { l := some (copyLabel (.finished 0)), var := w3, stk := T3 } := by
    simpa [k0, liftCfg, copyLabel] using
      (copy_run_lift k0
        { l := some (.dispatch 0 0), var := w1, stk := T1 }
        { l := some (.finished 0), var := w3, stk := T3 }
        (by simp) (by simpa [k0] using hcopy0))
  have hT3 : tableState T3 =
      runCommands n wit anc (program 0)
        (runCommands n wit anc (program 1)
          (runCommands n wit anc (program 2)
            (runCommands n wit anc tailProgram ([], [])))) := by
    rw [htable3, htable1, htable2, hT0]
  have hAmp : tableState T3 = (widths, bases) := by
    rw [hT3]
    simpa [widths, bases, ps, fullProgram, runCommands_append] using
      (run_fullProgram n wit anc)
  have hT3w : T3 (.inl (.inl (1 : Fin 14))) = widths := by
    simpa [tableState] using congrArg Prod.fst hAmp
  have hT3b : T3 (.inl (.inl (2 : Fin 14))) = bases := by
    simpa [tableState] using congrArg Prod.snd hAmp
  have hT38 : T3 (.inl (.inl (8 : Fin 14))) = [] := by
    rw [hframe3 _ (by simp [OutsideWrites]), hframe1 _ (by simp [OutsideWrites]),
      hframe2 _ (by simp [OutsideWrites]), hframe0 _ (by simp [OutsideWrites]), h8]
  have hT39 : T3 (.inl (.inl (9 : Fin 14))) = [] := by
    rw [hframe3 _ (by simp [OutsideWrites]), hframe1 _ (by simp [OutsideWrites]),
      hframe2 _ (by simp [OutsideWrites]), hframe0 _ (by simp [OutsideWrites]), h9]
  have hT310 : T3 (.inl (.inl (10 : Fin 14))) = [] := by
    rw [hframe3 _ (by simp [OutsideWrites]), hframe1 _ (by simp [OutsideWrites]),
      hframe2 _ (by simp [OutsideWrites]), hframe0 _ (by simp [OutsideWrites]), h10]
  obtain ⟨U, hmirror, hUw, hUb, hU8, hU9, hU10, hmirrorFrame⟩ :=
    ShiTMMirrorInit.both_run widths bases none T3
      hT3w hT3b hT38 hT39 hT310
  have hmirrorLift : run^[km]
      (some { l := some (mirrorLabel .startWidth), var := none, stk := T3 }) =
        some { l := some (mirrorLabel .done), var := none, stk := U } := by
    simpa [km, liftCfg, mirrorLabel] using
      (mirror_run_lift km
        { l := some .startWidth, var := none, stk := T3 }
        { l := some .done, var := none, stk := U }
        (by simp) (by simpa [km] using hmirror))
  have hA := iterTwo run kt 1 _ _ _ htailLift (tail_bridge w0 T0)
  have hB := iterTwo run (kt + 1) k2 _ _ _ hA hcopy2Lift
  have hC := iterTwo run ((kt + 1) + k2) 1 _ _ _ hB (copy2_bridge w2 T2)
  have hD := iterTwo run (((kt + 1) + k2) + 1) k1 _ _ _ hC hcopy1Lift
  have hE := iterTwo run ((((kt + 1) + k2) + 1) + k1) 1
    _ _ _ hD (copy1_bridge w1 T1)
  have hF := iterTwo run (((((kt + 1) + k2) + 1) + k1) + 1) k0
    _ _ _ hE hcopy0Lift
  have hG := iterTwo run ((((((kt + 1) + k2) + 1) + k1) + 1) + k0) 1
    _ _ _ hF (copy0_bridge w3 T3)
  have hH := iterTwo run (((((((kt + 1) + k2) + 1) + k1) + 1) + k0) + 1) km
    _ _ _ hG hmirrorLift
  have hI := iterTwo run ((((((((kt + 1) + k2) + 1) + k1) + 1) + k0) + 1) + km) 1
    _ _ _ hH (mirror_bridge none U)
  have hUret : Retained n wit anc U := by
    rcases hret3 with ⟨hr0, hr1, hr2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hmirrorFrame (.inr (0 : Fin 4)) (by simp) (by simp)
        (by simp) (by simp) (by simp)]
      exact hr0
    · rw [hmirrorFrame (.inr (1 : Fin 4)) (by simp) (by simp)
        (by simp) (by simp) (by simp)]
      exact hr1
    · rw [hmirrorFrame (.inr (2 : Fin 4)) (by simp) (by simp)
        (by simp) (by simp) (by simp)]
      exact hr2
  have hU3 : U (.inl (.inl (3 : Fin 14))) = [] := by
    rw [hmirrorFrame _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hscratch3
  refine ⟨U, ((((((((kt + 1) + k2) + 1) + k1) + 1) + k0) + 1) + km) + 1,
    hI, hUw, hUb, hU8, hU9, hU10, hUret, hU3, ?_, ?_⟩
  · intro j hj hj8 hj9 hj10
    have hj1 : j ≠ .inl (.inl (1 : Fin 14)) := hj.1
    have hj2 : j ≠ .inl (.inl (2 : Fin 14)) := hj.2.1
    have hj3 : j ≠ .inl (.inl (10 : Fin 14)) := hj10
    rw [hmirrorFrame j hj1 hj2 hj8 hj9 hj3,
      hframe3 j hj, hframe1 j hj, hframe2 j hj, hframe0 j hj]
  · dsimp [stageCost, kt, k2, k1, k0, km, widths, bases, ps]
    omega

end ShiTMStageChain
