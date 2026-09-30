import «AMPUNI-piece-param-tail-command»
import «AMPUNI-piece-controller-cost-run»
import «AMPUNI-piece-tail-program»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceParam

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule
open ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem active_suffix (commands : List Command) (pc : PC)
    (command : Command) (rest : List Command)
    (hlength : commands.length ≤ 64)
    (hsuffix : commands.drop pc.val = command :: rest) :
    commandAt commands pc.val = some command ∧
      commands.drop (nextPC pc).val = rest := by
  have hcommand : commandAt commands pc.val = some command := by
    rw [commandAt_eq_head_drop, hsuffix]
    rfl
  refine ⟨hcommand, ?_⟩
  have hpos := commandAt_some_lt commands pc.val command hcommand
  rw [nextPC_no_wrap pc (by omega), drop_succ_eq_tail, hsuffix]
  rfl

/-- A bounded fixed command list executes with the pure interpreter's table
effect, exact command cost, and a frame for every non-command stack. -/
theorem run_suffix_cost (commands xs : List Command) (copy : Fin 3)
    (n wit anc : Nat) (pc : PC) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hlength : commands.length ≤ 64)
    (hsuffix : commands.drop pc.val = xs)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig) (pc' : PC),
      (runFor commands)^[scheduleCost n wit anc xs]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy pc'), var := v', stk := U }
      ∧ pc'.val = pc.val + xs.length
      ∧ tableState U = runCommands n wit anc xs (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  induction xs generalizing pc v S with
  | nil =>
      exact ⟨S, v, pc, rfl, by simp, by simp [runCommands], hret,
        hscratch, by intro j _; rfl⟩
  | cons command xs ih =>
      obtain ⟨hcommand, hsuffix'⟩ :=
        active_suffix commands pc command xs hlength hsuffix
      obtain ⟨T, w, hfirst, htable, hretT, hscratchT, hframeT⟩ :=
        dispatch_command commands copy pc command n wit anc v S
          hcommand hret hscratch
      obtain ⟨U, w', pc', hrest, hpc', htable', hretU,
        hscratchU, hframeU⟩ :=
        ih (nextPC pc) w T hsuffix' hretT hscratchT
      refine ⟨U, w', pc', ?_, ?_, ?_, hretU, hscratchU, ?_⟩
      · change (runFor commands)^[commandCost n wit anc command +
          scheduleCost n wit anc xs]
          (some { l := some (.dispatch copy pc), var := v, stk := S }) =
            some { l := some (.dispatch copy pc'), var := w', stk := U }
        exact iterTwo (runFor commands) (commandCost n wit anc command)
          (scheduleCost n wit anc xs) _ _ _ hfirst hrest
      · have hpos := commandAt_some_lt commands pc.val command hcommand
        have hnext := nextPC_no_wrap pc (by omega)
        simp only [List.length_cons] at *
        omega
      · change tableState U =
          runCommands n wit anc xs
            (commandStep n wit anc command (tableState S))
        rw [htable] at htable'
        exact htable'
      · intro j hj
        rw [hframeU j hj, hframeT j hj]

theorem run_program_cost (commands : List Command) (copy : Fin 3)
    (n wit anc : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hlength : commands.length ≤ 64)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig) (pc' : PC),
      (runFor commands)^[scheduleCost n wit anc commands]
        (some { l := some (.dispatch copy 0), var := v, stk := S }) =
          some { l := some (.dispatch copy pc'), var := v', stk := U }
      ∧ pc'.val = commands.length
      ∧ tableState U = runCommands n wit anc commands (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  simpa using run_suffix_cost commands commands copy n wit anc 0 v S
    hlength (by simp) hret hscratch

theorem terminal_dispatch_step (commands : List Command) (copy : Fin 3)
    (pc : PC) (v : Sig) (S : ∀ k, List (TopGam k))
    (hpc : pc.val = commands.length) :
    (runFor commands)^[1]
      (some { l := some (.dispatch copy pc), var := v, stk := S }) =
        some { l := some (.finished copy), var := v, stk := S } := by
  have hnone : commandAt commands pc.val = none := by
    rw [hpc, commandAt_eq_head_drop, List.drop_length]
    rfl
  simp [runFor, machineFor, hnone, step, stepAux]

theorem run_program_finished (commands : List Command) (copy : Fin 3)
    (n wit anc : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hlength : commands.length ≤ 64)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      (runFor commands)^[scheduleCost n wit anc commands + 1]
        (some { l := some (.dispatch copy 0), var := v, stk := S }) =
          some { l := some (.finished copy), var := v', stk := U }
      ∧ tableState U = runCommands n wit anc commands (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  obtain ⟨U, v', pc', hrun, hpc, htable, hretU, hscratchU, hframe⟩ :=
    run_program_cost commands copy n wit anc v S hlength hret hscratch
  refine ⟨U, v', ?_, htable, hretU, hscratchU, hframe⟩
  have hlast := terminal_dispatch_step commands copy pc' v' U hpc
  exact iterTwo (runFor commands) (scheduleCost n wit anc commands) 1
    _ _ _ hrun hlast

/-- The first actual machine-run checkpoint for the complete amplification
layout: construct the terminal one-wire piece from empty width/base tables. -/
theorem tail_program_finished (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = [])
    (hwidth : S (.inl (.inl (1 : Fin 14))) = [])
    (hbase : S (.inl (.inl (2 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      (runFor tailProgram)^[scheduleCost n wit anc tailProgram + 1]
        (some { l := some (.dispatch 0 0), var := v, stk := S }) =
          some { l := some (.finished 0), var := v', stk := U }
      ∧ tableState U =
          (pieceCells Prod.fst (copyTail n wit anc),
           pieceCells Prod.snd (copyTail n wit anc))
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  obtain ⟨U, v', hrun, htable, hretU, hscratchU, hframe⟩ :=
    run_program_finished tailProgram 0 n wit anc v S
      tailProgram_length_le_64 hret hscratch
  refine ⟨U, v', hrun, ?_, hretU, hscratchU, hframe⟩
  rw [htable]
  simpa [tableState, hwidth, hbase] using
    (run_tailProgram n wit anc [] [])

end ShiTMPieceParam
