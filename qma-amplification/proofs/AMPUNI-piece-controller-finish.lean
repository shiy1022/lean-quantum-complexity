import «AMPUNI-piece-controller-cost-bound»
import «AMPUNI-piece-controller-program-tables»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem commandAt_length_none (copy : Fin 3) :
    commandAt (program copy) (program copy).length = none := by
  rw [commandAt_eq_head_drop, List.drop_length]
  rfl

theorem terminal_dispatch_step (copy : Fin 3) (pc : PC)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hpc : pc.val = (program copy).length) :
    run^[1] (some { l := some (.dispatch copy pc), var := v, stk := S }) =
      some { l := some (.finished copy), var := v, stk := S } := by
  have hnone : commandAt (program copy) pc.val = none := by
    rw [hpc]
    exact commandAt_length_none copy
  simp [run, machine, hnone, step, stepAux]

/-- The finite scheduler reaches its terminal state after the exact command
cost plus one exit step, retaining the three unary headers and empty scratch. -/
theorem run_program_finished (copy : Fin 3) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[scheduleCost n wit anc (program copy) + 1]
        (some { l := some (.dispatch copy 0), var := v, stk := S }) =
          some { l := some (.finished copy), var := v', stk := U }
      ∧ tableState U =
          runCommands n wit anc (program copy) (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = [] := by
  obtain ⟨U, v', pc', hrun, hpc, htable, hretU, hscratchU⟩ :=
    run_program_cost copy n wit anc v S hret hscratch
  refine ⟨U, v', ?_, htable, hretU, hscratchU⟩
  have hlast := terminal_dispatch_step copy pc' v' U hpc
  exact iterTwo run (scheduleCost n wit anc (program copy)) 1
    _ _ _ hrun hlast

end ShiTMPieceController
