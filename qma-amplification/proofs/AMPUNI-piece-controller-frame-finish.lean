import «AMPUNI-piece-controller-frame-run»
import «AMPUNI-piece-controller-finish»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The terminal copy-program theorem with both its table semantics and its
frame. This keeps the input circuit and the future mirror stacks intact. -/
theorem run_program_finished_frame (copy : Fin 3) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[scheduleCost n wit anc (program copy) + 1]
        (some { l := some (.dispatch copy 0), var := v, stk := S }) =
          some { l := some (.finished copy), var := v', stk := U }
      ∧ tableState U = runCommands n wit anc (program copy) (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  obtain ⟨U, v', hrun, htable, hretU, hscratchU⟩ :=
    run_program_finished copy n wit anc v S hret hscratch
  obtain ⟨W, w, pc, hframeRun, hpc, _, _, hframe⟩ :=
    run_program_frame copy n wit anc v S hret hscratch
  have hterminal := terminal_dispatch_step copy pc w W hpc
  have hrunW : run^[scheduleCost n wit anc (program copy) + 1]
      (some { l := some (.dispatch copy 0), var := v, stk := S }) =
        some { l := some (.finished copy), var := w, stk := W } :=
    iterTwo run (scheduleCost n wit anc (program copy)) 1
      _ _ _ hframeRun hterminal
  have hUW : U = W := by
    have h := hrun.symm.trans hrunW
    exact congrArg (fun c : Cfg TopGam Label Sig => c.stk) (Option.some.inj h)
  refine ⟨U, v', hrun, htable, hretU, hscratchU, ?_⟩
  intro j hj
  rw [hUW]
  exact hframe j hj

end ShiTMPieceController
