import «AMPUNI-boolean-controller-wrapper»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMBooleanWrapper
open ShiTMLayoutMachine (Cell Sig bit)
open ShiTMRetainedTop
open ShiTMBooleanIO (K Gam input output source scratch accumulator)
variable {L : Type} [DecidableEq L] [Fintype L]

/-- Turn a verified typed body run into an actual Boolean-boundary run from
`initList` to canonical `haltList`. The body emits a reversed bit accumulator;
all remaining work stacks may be arbitrary and are drained by finalization. -/
theorem valid_input_run (M : L → Stmt TopGam L Sig) (main terminal : L)
    (hterminal : M terminal = .halt) (xs ys : List Bool) (bodySteps : Nat)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hr : (ShiTMSubroutine.run M)^[bodySteps]
      (some ⟨some main, none, initialTop xs⟩) = some ⟨some terminal, v, S⟩)
    (ho : S cellOutput = (ys.map bit).reverse) :
    ∃ steps : Nat,
      steps ≤ 2*xs.length+bodySteps+ys.length+
        ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo
          (ShiTMIOFrame.extendStacks S (fun _ => []))+7 ∧
      (run M main terminal)^[steps]
        (some (Turing.initList (finiteMachine M main terminal) xs)) =
          some (Turing.haltList (finiteMachine M main terminal) ys) := by
  let U := ShiTMIOFrame.extendStacks S (fun _ => [])
  have hl := loader_run M main terminal xs
  have hi : (run M main terminal)^[1]
      (some ⟨some (.inl .ready), none, loadedIO xs⟩) =
      some ⟨some (bodyLabel main), none, loadedIO xs⟩ := by rfl
  have hb := body_run M main terminal hterminal xs bodySteps v S hr
  have hh : (run M main terminal)^[1] (some ⟨some (bodyLabel terminal), v, U⟩) =
      some ⟨some (finalLabel (.inl .writeOutput)), v, U⟩ := by
    simp [run, ShiTMSubroutine.run, machine, bodyLabel, step, stepAux]
  obtain ⟨finishSteps, hfinishBound, hfinish⟩ := ShiTMBooleanFinal.final_output_run ys v U ho rfl
  have hf := ShiTMSubroutine.run_iter_lift ShiTMBooleanFinal.machine (machine M main terminal)
    finalLabel (by intro l; rfl) finishSteps
    (some ⟨some (.inl .writeOutput), v, U⟩)
  change (run M main terminal)^[finishSteps]
      (some ⟨some (finalLabel (.inl .writeOutput)), v, U⟩) =
      (ShiTMBooleanFinal.run^[finishSteps]
        (some ⟨some (.inl .writeOutput), v, U⟩)).map (ShiTMSubroutine.cfg finalLabel) at hf
  rw [hfinish] at hf
  have hf' : (run M main terminal)^[finishSteps]
      (some ⟨some (finalLabel (.inl .writeOutput)), v, U⟩) =
      some (Turing.haltList (finiteMachine M main terminal) ys) := by
    have heq : ShiTMSubroutine.cfg (finalLabel : ShiTMBooleanFinal.Label → Label L)
        (Turing.haltList ShiTMBooleanFinal.finiteMachine ys) =
        Turing.haltList (finiteMachine M main terminal) ys := by rfl
    change (run M main terminal)^[finishSteps]
        (some ⟨some (finalLabel (.inl .writeOutput)), v, U⟩) =
        some (ShiTMSubroutine.cfg (finalLabel : ShiTMBooleanFinal.Label → Label L)
          (Turing.haltList ShiTMBooleanFinal.finiteMachine ys)) at hf
    rw [heq] at hf
    exact hf
  have hinit : (Turing.initList (finiteMachine M main terminal) xs : Cfg Gam (Label L) Sig) =
      ⟨some (.inl .readInput), none, initialIO xs⟩ := by
    dsimp only [Turing.initList, finiteMachine]
    congr 1
    funext k
    by_cases hk : k = input
    · subst k; simp [initialIO]
    · simp [initialIO, hk]
  let steps := (((2*xs.length+2)+1)+bodySteps)+1+finishSteps
  refine ⟨steps, ?_, ?_⟩
  · dsimp [steps]
    dsimp [U] at hfinishBound
    omega
  · rw [hinit]
    have h1 := ShiTMFanout.iterTwo (run M main terminal) _ _ _ _ _ hl hi
    have h2 := ShiTMFanout.iterTwo (run M main terminal) _ _ _ _ _ h1 hb
    have h3 := ShiTMFanout.iterTwo (run M main terminal) _ _ _ _ _ h2 hh
    exact ShiTMFanout.iterTwo (run M main terminal) _ _ _ _ _ h3 hf'

/-- The same boundary construction in mathlib's actual timed-output interface.
The normalizer body and its output equation remain explicit hypotheses. -/
theorem valid_input_outputs (M : L → Stmt TopGam L Sig) (main terminal : L)
    (hterminal : M terminal = .halt) (xs ys : List Bool) (bodySteps : Nat)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hr : (ShiTMSubroutine.run M)^[bodySteps]
      (some ⟨some main, none, initialTop xs⟩) = some ⟨some terminal, v, S⟩)
    (ho : S cellOutput = (ys.map bit).reverse) :
    Nonempty (Turing.TM2OutputsInTime (finiteMachine M main terminal) xs (some ys)
      (2*xs.length+bodySteps+ys.length+
        ShiTMBooleanCleanup.suffixCost ShiTMBooleanCleanup.todo
          (ShiTMIOFrame.extendStacks S (fun _ => []))+7)) := by
  obtain ⟨steps, hb, hr'⟩ := valid_input_run M main terminal hterminal xs ys bodySteps v S hr ho
  exact ⟨⟨⟨steps, hr'⟩, hb⟩⟩

end ShiTMBooleanWrapper
