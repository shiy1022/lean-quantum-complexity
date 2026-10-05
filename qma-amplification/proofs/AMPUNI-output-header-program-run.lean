import «AMPUNI-output-header-command»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

private theorem active_suffix (pc : PC) (command : Command)
    (rest : List Command)
    (hsuffix : program.drop pc.val = command :: rest) :
    commandAt program pc.val = some command ∧
      program.drop (nextPC pc).val = rest := by
  have hc : commandAt program pc.val = some command := by
    rw [commandAt_eq_head_drop, hsuffix]
    rfl
  refine ⟨hc, ?_⟩
  have hnext := active_command_no_wrap pc command hc
  calc
    program.drop (nextPC pc).val = program.drop (pc.val + 1) := by rw [hnext]
    _ = (program.drop pc.val).drop 1 := by rw [List.drop_drop]
    _ = rest := by rw [hsuffix]; rfl

/-- A suffix of the fixed program executes with the pure schedule's exact
stack effect, while retaining all three unary sources and clearing scratch. -/
theorem run_suffix_cost (xs : List Command) (n wit anc : Nat)
    (pc : PC) (v : Sig) (S : ∀ k, List (TopGam k))
    (hsuffix : program.drop pc.val = xs)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig) (pc' : PC),
      run^[scheduleCost n wit anc xs]
        (some { l := some (.dispatch pc), var := v, stk := S }) =
          some { l := some (.dispatch pc'), var := v', stk := U }
      ∧ pc'.val = pc.val + xs.length
      ∧ U (.inl (.inl (13 : Fin 14))) =
          eval n wit anc xs (S (.inl (.inl (13 : Fin 14))))
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  induction xs generalizing pc v S with
  | nil =>
      exact ⟨S, v, pc, rfl, by simp, by simp [eval], hret, hscratch,
        by intro j _; rfl⟩
  | cons command xs ih =>
      obtain ⟨hcommand, hsuffix'⟩ := active_suffix pc command xs hsuffix
      obtain ⟨T, w, hfirst, hT13, hretT, hscratchT, hframeT⟩ :=
        dispatch_command pc command n wit anc v S hcommand hret hscratch
      obtain ⟨U, w', pc', hrest, hpc', hU13, hretU, hscratchU,
        hframeU⟩ := ih (nextPC pc) w T hsuffix' hretT hscratchT
      refine ⟨U, w', pc', ?_, ?_, ?_, hretU, hscratchU, ?_⟩
      · change run^[commandCost n wit anc command + scheduleCost n wit anc xs]
          (some { l := some (.dispatch pc), var := v, stk := S }) =
            some { l := some (.dispatch pc'), var := w', stk := U }
        exact iterTwo run (commandCost n wit anc command)
          (scheduleCost n wit anc xs) _ _ _ hfirst hrest
      · have hnext := active_command_no_wrap pc command hcommand
        simp only [List.length_cons] at *
        omega
      · change U (.inl (.inl (13 : Fin 14))) =
          eval n wit anc xs
            (cells n wit anc command ++ S (.inl (.inl (13 : Fin 14))))
        rw [← hT13]
        exact hU13
      · intro j hj
        rw [hframeU j hj, hframeT j hj]

theorem run_program_cost (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig) (pc' : PC),
      run^[scheduleCost n wit anc program]
        (some { l := some (.dispatch 0), var := v, stk := S }) =
          some { l := some (.dispatch pc'), var := v', stk := U }
      ∧ pc'.val = program.length
      ∧ U (.inl (.inl (13 : Fin 14))) =
          eval n wit anc program (S (.inl (.inl (13 : Fin 14))))
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  simpa using run_suffix_cost program n wit anc 0 v S
    (by simp) hret hscratch

theorem run_program_finished (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[scheduleCost n wit anc program + 1]
        (some { l := some (.dispatch 0), var := v, stk := S }) =
          some { l := some .finished, var := v', stk := U }
      ∧ U (.inl (.inl (13 : Fin 14))) =
          eval n wit anc program (S (.inl (.inl (13 : Fin 14))))
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  obtain ⟨U, v', pc', hrun, hpc, hout, hretU, hscratchU, hframe⟩ :=
    run_program_cost n wit anc v S hret hscratch
  have hnone : commandAt program pc'.val = none := by
    rw [hpc, commandAt_eq_head_drop, List.drop_length]
    rfl
  have hlast := terminal_dispatch_step pc' v' U hnone
  exact ⟨U, v', iterTwo run (scheduleCost n wit anc program) 1
    _ _ _ hrun hlast, hout, hretU, hscratchU, hframe⟩

end ShiTMOutputHeader
