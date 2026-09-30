import «AMPUNI-repeat-loop-induction»
import «AMPUNI-constructive-repeatable-runs»
import «AMPUNI-repeat-finish-shape»
import «AMPUNI-repeat-concrete-controller»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section
namespace ShiTMConstructiveConcrete
open ShiClassQMA ShiClassQMAU ShiClassQMAAmpX
  ShiQMAVariableRounds

noncomputable def controllerMachine (k : Nat) := by
  letI : DecidableEq (source k).K := (source k).kDecidableEq
  letI : DecidableEq (source k).Λ := Classical.decEq _
  exact ShiTMRepeatController.machine
    (liftedSource (source k).m)
    (source k).main (ShiTMRepeatConcrete.terminal k)
    (source k).k₀ (source k).k₁ id id

/-- The fixed finite QMA controller performs every requested iteration
correctly when its four auxiliary stacks initially contain the prescribed
unary header and counter. This is the exact multi-round run; loading the
counter from the raw input is a separate construction. -/
theorem constructive_preloaded_loop_runs :
    ∃ k C : Nat, ∀ (F : QMAFamily) (n q : Nat) (b parity : Bool),
      ∃ times : Nat → Nat,
      (∀ r, times r ≤ C *
        ((ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n).length + 1) ^ 2) ∧
      ∃ t : Nat, ∃ S : ∀ j,
        List (ShiTMRepeatController.Gam
          (ShiTMRepeatConcrete.source k).Γ j),
        (ShiTMSubroutine.run (controllerMachine k))^[t]
          (some (ShiTMRepeatController.loopInput
            (ShiTMRepeatConcrete.source k).main
            (ShiTMRepeatConcrete.source k).k₀
            (parity, (ShiTMRepeatConcrete.source k).initialState.2)
            (ShiBQP.encNat n ++ encQMAFamilyAt F n)
            b n q)) =
          some ⟨none,
            (none, (parity, (ShiTMRepeatConcrete.source k).initialState.2)), S⟩ ∧
        S (.inl (ShiTMRepeatConcrete.source k).k₁) =
          encQMAFamilyAt (iter F (q + 1)) n ∧
        (∀ j : (ShiTMRepeatConcrete.source k).K,
          j ≠ (ShiTMRepeatConcrete.source k).k₁ → S (.inl j) = []) ∧
        (∀ h : ShiTMRepeatController.Aux, S (.inr h) = []) ∧
        t ≤ ShiTMRepeatController.preloadedCost n
          (fun r => (encQMAFamilyAt (ampFamilyX (iter F r)) n).length)
          times 0 q := by
  obtain ⟨k, C, hk⟩ := lifted_repeatable_round_runs
  letI : DecidableEq (ShiTMRepeatConcrete.source k).K :=
    (ShiTMRepeatConcrete.source k).kDecidableEq
  letI : DecidableEq (ShiTMRepeatConcrete.source k).Λ :=
    Classical.decEq _
  refine ⟨k, C, ?_⟩
  intro F n q b parity
  let times : Nat → Nat := fun r =>
    Classical.choose (hk F n r parity)
  have htimes (r : Nat) : times r ≤ C *
      ((ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n).length + 1) ^ 2 :=
    (Classical.choose_spec (hk F n r parity)).2
  refine ⟨times, htimes, ?_⟩
  let code (r : Nat) : List Bool :=
    ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n
  let result (r : Nat) : List Bool :=
    encQMAFamilyAt (ampFamilyX (iter F r)) n
  let finish (r : Nat) := liftedCfg parity
    (ShiTMRepeatFueled.activeFinish
      ShiTMNormalizedEntry.booleanMachine (Equiv.refl Bool) k (result r))
  have hcode (r : Nat) : code (r + 1) =
      ((List.replicate n true ++ false :: (result r).map id).map id) := by
    simp [code, result, iter, ShiBQP.encNat]
  have hrun (r : Nat) :
      (ShiTMSubroutine.run (liftedSource (source k).m))^[times r]
        (some ⟨some (ShiTMRepeatConcrete.source k).main,
          (none, (parity, (ShiTMRepeatConcrete.source k).initialState.2)),
          ShiTMRepeatController.sourceInput
            (ShiTMRepeatConcrete.source k).k₀ (code r)⟩) =
        some (finish r) := by
    have h := (Classical.choose_spec (hk F n r parity)).1
    have hstart0 :
        Turing.initList (ShiTMRepeatConcrete.source k) (code r) =
          ⟨some (ShiTMRepeatConcrete.source k).main,
            (none, (ShiTMRepeatConcrete.source k).initialState.2),
            ShiTMRepeatController.sourceInput
              (ShiTMRepeatConcrete.source k).k₀ (code r)⟩ := by
      unfold Turing.initList ShiTMRepeatController.sourceInput
      congr 1
      funext j
      by_cases hj : j = (ShiTMRepeatConcrete.source k).k₀
      · subst j
        simp [Function.update]
        rfl
      · simp [Function.update, hj]
    have hstart : liftedCfg parity
        (Turing.initList (ShiTMRepeatConcrete.source k) (code r)) =
          ⟨some (ShiTMRepeatConcrete.source k).main,
            (none, (parity, (ShiTMRepeatConcrete.source k).initialState.2)),
            ShiTMRepeatController.sourceInput
              (ShiTMRepeatConcrete.source k).k₀ (code r)⟩ := by
      rw [hstart0]
      rfl
    rw [←hstart]
    exact h
  have hlabel (r : Nat) :
      (finish r).l = some (ShiTMRepeatConcrete.terminal k) := by
    rfl
  have hstate (r : Nat) :
      (finish r).var =
        (none, (parity, (ShiTMRepeatConcrete.source k).initialState.2)) := by
    rfl
  have houtput (r : Nat) :
      (finish r).stk (ShiTMRepeatConcrete.source k).k₁ = result r := by
    simpa [finish, liftedCfg, ShiTMStateReindex.cfg,
      ShiTMStateFrame.cfg, result, ShiTMRepeatConcrete.source] using
      (ShiTMRepeatFueled.activeFinish_output
        ShiTMNormalizedEntry.booleanMachine (Equiv.refl Bool) k (result r))
  have hclean (r : Nat) (j : (ShiTMRepeatConcrete.source k).K)
      (hj : j ≠ (ShiTMRepeatConcrete.source k).k₁) :
      (finish r).stk j = [] := by
    simpa [finish, liftedCfg, ShiTMStateReindex.cfg,
      ShiTMStateFrame.cfg, ShiTMRepeatConcrete.source] using
      (ShiTMRepeatFueled.activeFinish_other_empty
        ShiTMNormalizedEntry.booleanMachine (Equiv.refl Bool) k (result r)
        j hj)
  have hio : (ShiTMRepeatConcrete.source k).k₀ ≠
      (ShiTMRepeatConcrete.source k).k₁ := by
    intro he
    cases he
  have hhalt : liftedSource (source k).m
      (ShiTMRepeatConcrete.terminal k) = .halt := by
    simp [liftedSource, ShiTMStateReindex.machine,
      ShiTMStateFrame.machine, ShiTMStateReindex.stmt,
      ShiTMStateFrame.stmt,
      ShiTMRepeatConcrete.terminal_halt]
  obtain ⟨t, S, hloop, hout, hother, haux, hcost⟩ :=
    ShiTMRepeatController.preloaded_loop_runs
      (liftedSource (source k).m)
      (ShiTMRepeatConcrete.source k).main
      (ShiTMRepeatConcrete.terminal k)
      (ShiTMRepeatConcrete.source k).k₀
      (ShiTMRepeatConcrete.source k).k₁ hio id id
      hhalt
      n (parity, (ShiTMRepeatConcrete.source k).initialState.2)
      code result times finish hcode hrun hlabel hstate houtput hclean
      0 q b
  refine ⟨t, S, ?_, ?_, hother, haux, ?_⟩
  · change
      (ShiTMSubroutine.run (controllerMachine k))^[t]
        (some (ShiTMRepeatController.loopInput
          (ShiTMRepeatConcrete.source k).main
          (ShiTMRepeatConcrete.source k).k₀
          (parity, (ShiTMRepeatConcrete.source k).initialState.2)
          (ShiBQP.encNat n ++ encQMAFamilyAt F n) b n q)) =
        some ⟨none,
          (none, (parity, (ShiTMRepeatConcrete.source k).initialState.2)), S⟩
    change
      (ShiTMSubroutine.run (controllerMachine k))^[t]
        (some (ShiTMRepeatController.loopInput
          (ShiTMRepeatConcrete.source k).main
          (ShiTMRepeatConcrete.source k).k₀
          (parity, (ShiTMRepeatConcrete.source k).initialState.2)
          (code 0) b n q)) =
        some ⟨none,
          (none, (parity, (ShiTMRepeatConcrete.source k).initialState.2)), S⟩ at hloop
    simpa [code, iter] using hloop
  · simpa [result, iter] using hout
  · change t ≤ ShiTMRepeatController.preloadedCost n
        (fun r => (result r).length) times 0 q
    exact hcost

end ShiTMConstructiveConcrete
