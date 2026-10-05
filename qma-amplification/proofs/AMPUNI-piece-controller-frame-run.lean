import «AMPUNI-piece-controller-frame-command»
import «AMPUNI-piece-controller-cost-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

private theorem same_stack {x : Option (Cfg TopGam Label Sig)}
    {p q : Label} {v w : Sig}
    {S T : ∀ k, List (TopGam k)}
    (hS : x = some { l := some p, var := v, stk := S })
    (hT : x = some { l := some q, var := w, stk := T }) : S = T := by
  have h := hS.symm.trans hT
  exact congrArg (fun c : Cfg TopGam Label Sig => c.stk) (Option.some.inj h)

/-- The fixed scheduler preserves every stack outside its table, scratch, and
retained-header write set, for an arbitrary active command suffix. -/
theorem run_suffix_frame (copy : Fin 3) (xs : List Command)
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
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  induction xs generalizing pc v S with
  | nil =>
      exact ⟨S, v, pc, rfl, by simp, hret, hscratch,
        by intro j _; rfl⟩
  | cons command xs ih =>
      obtain ⟨hcommand, hsuffix'⟩ :=
        active_suffix copy pc command xs hsuffix
      obtain ⟨T, w, hfirst, _, hretT, hscratchT⟩ :=
        dispatch_command copy pc command n wit anc v S
          hcommand hret hscratch
      obtain ⟨W, z, hfirstW, hframeW⟩ :=
        dispatch_command_frame copy pc command n wit anc v S
          hcommand hret hscratch
      have hTW : T = W := same_stack hfirst hfirstW
      have hframeT : ∀ j, OutsideWrites j → T j = S j := by
        intro j hj
        rw [hTW]
        exact hframeW j hj
      obtain ⟨U, w', pc', hrest, hpc', hretU, hscratchU, hframeU⟩ :=
        ih (nextPC pc) w T hsuffix' hretT hscratchT
      refine ⟨U, w', pc', ?_, ?_, hretU, hscratchU, ?_⟩
      · change run^[commandCost n wit anc command + scheduleCost n wit anc xs]
          (some { l := some (.dispatch copy pc), var := v, stk := S }) =
            some { l := some (.dispatch copy pc'), var := w', stk := U }
        exact iterTwo run (commandCost n wit anc command)
          (scheduleCost n wit anc xs) _ _ _ hfirst hrest
      · have hnext := active_command_no_wrap copy pc command hcommand
        simp only [List.length_cons] at *
        omega
      · intro j hj
        rw [hframeU j hj, hframeT j hj]

theorem run_program_frame (copy : Fin 3) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig) (pc' : PC),
      run^[scheduleCost n wit anc (program copy)]
        (some { l := some (.dispatch copy 0), var := v, stk := S }) =
          some { l := some (.dispatch copy pc'), var := v', stk := U }
      ∧ pc'.val = (program copy).length
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  simpa using run_suffix_frame copy (program copy) n wit anc 0 v S
    (by simp) hret hscratch

end ShiTMPieceController
