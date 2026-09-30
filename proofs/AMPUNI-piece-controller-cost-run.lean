import «AMPUNI-piece-controller-program-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

def scheduleCost (n wit anc : Nat) (xs : List Command) : Nat :=
  (xs.map (commandCost n wit anc)).sum

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Exact runtime refinement of `run_suffix`; the cost is the sum of the
fixed command costs, so a polynomial clock can be derived separately. -/
theorem run_suffix_cost (copy : Fin 3) (xs : List Command)
    (n wit anc : Nat) (pc : PC) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsuffix : (program copy).drop pc.val = xs)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig) (pc' : PC),
      run^[scheduleCost n wit anc xs]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy pc'), var := v', stk := U }
      ∧ pc'.val = pc.val + xs.length
      ∧ tableState U = runCommands n wit anc xs (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = [] := by
  induction xs generalizing pc v S with
  | nil =>
      exact ⟨S, v, pc, rfl, by simp, by simp [runCommands], hret, hscratch⟩
  | cons command xs ih =>
      obtain ⟨hcommand, hsuffix'⟩ :=
        active_suffix copy pc command xs hsuffix
      obtain ⟨T, w, hfirst, htable, hretT, hscratchT⟩ :=
        dispatch_command copy pc command n wit anc v S
          hcommand hret hscratch
      obtain ⟨U, w', pc', hrest, hpc', htable', hretU, hscratchU⟩ :=
        ih (nextPC pc) w T hsuffix' hretT hscratchT
      refine ⟨U, w', pc', ?_, ?_, ?_, hretU, hscratchU⟩
      · change run^[commandCost n wit anc command + scheduleCost n wit anc xs]
          (some { l := some (.dispatch copy pc), var := v, stk := S }) =
            some { l := some (.dispatch copy pc'), var := w', stk := U }
        exact iterTwo run (commandCost n wit anc command)
          (scheduleCost n wit anc xs) _ _ _ hfirst hrest
      · have hnext := active_command_no_wrap copy pc command hcommand
        simp only [List.length_cons] at *
        omega
      · change tableState U =
          runCommands n wit anc xs
            (commandStep n wit anc command (tableState S))
        rw [htable] at htable'
        exact htable'

theorem run_program_cost (copy : Fin 3) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig) (pc' : PC),
      run^[scheduleCost n wit anc (program copy)]
        (some { l := some (.dispatch copy 0), var := v, stk := S }) =
          some { l := some (.dispatch copy pc'), var := v', stk := U }
      ∧ pc'.val = (program copy).length
      ∧ tableState U =
          runCommands n wit anc (program copy) (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = [] := by
  simpa using run_suffix_cost copy (program copy) n wit anc 0 v S
    (by simp) hret hscratch

end ShiTMPieceController
