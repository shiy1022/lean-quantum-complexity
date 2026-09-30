import «AMPUNI-constructive-preloaded-loop»
import «AMPUNI-constructive-controller-compose»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section
namespace ShiTMConstructiveConcrete
open ShiClassQMA ShiClassQMAU ShiClassQMAAmpX
  ShiQMAVariableRounds

/-- The integrated finite program computes the exact amplified verifier
encoding on every clean raw input. The remaining polynomial-time package
must bound this witness time and totalize malformed inputs. -/
theorem constructive_valid_rounds :
    ∃ k C : Nat, ∀ (F : QMAFamily) (p : Polynomial ℕ) (n : Nat),
      let tm := source k
      let code := encQMAFamilyAt F n
      let raw := ShiBQP.encNat n ++ code
      let q := ShiQMAConstructiveSchedule.rounds p n - 1
      ∀ S₀ : ∀ j, List (ShiTMRepeatController.Gam tm.Γ j),
      S₀ (.inl tm.k₀) = raw →
      (∀ j : tm.K, j ≠ tm.k₀ → S₀ (.inl j) = []) →
      (∀ h : ShiTMRepeatController.Aux, S₀ (.inr h) = []) →
      ∃ times : Nat → Nat,
      (∀ r, times r ≤ C *
        ((ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n).length + 1) ^ 2) ∧
      ∃ t : Nat, ∃ parity : Bool,
      ∃ S' : ∀ j, List (ShiTMRepeatController.Gam tm.Γ j),
        (ShiTMSubroutine.run (finiteMachine k p).m)^[
              2 * n + 3 +
                (ShiTMUnaryLogCost.work (n + 1) + n + 3) + t]
          (some ⟨some ShiTMConstructiveIntegrated.scan,
            (none, (true, tm.initialState.2)), S₀⟩) =
          some ⟨none, (none, (parity, tm.initialState.2)), S'⟩ ∧
        S' (.inl tm.k₁) =
          encQMAFamilyAt
            (iter F (ShiQMAConstructiveSchedule.rounds p n)) n ∧
        (∀ j : tm.K, j ≠ tm.k₁ → S' (.inl j) = []) ∧
        (∀ h : ShiTMRepeatController.Aux, S' (.inr h) = []) ∧
        t ≤ ShiTMRepeatController.preloadedCost n
          (fun r => (encQMAFamilyAt (ampFamilyX (iter F r)) n).length)
          times 0 q := by
  obtain ⟨k, C, hk⟩ := constructive_preloaded_loop_runs
  refine ⟨k, C, ?_⟩
  intro F p n
  dsimp only
  let tm := source k
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : DecidableEq tm.Λ := Classical.decEq _
  intro S₀ hi hbase haux₀
  let q := ShiQMAConstructiveSchedule.rounds p n - 1
  have hi' : S₀ (.inl tm.k₀) =
      List.replicate n true ++ false :: encQMAFamilyAt F n := by
    simpa [tm, ShiBQP.encNat] using hi
  obtain ⟨parity, hstart⟩ :=
    ShiTMConstructiveIntegrated.valid_prefix_to_preloaded_bank
      p (liftedSource tm.m) tm.main
      (ShiTMRepeatConcrete.terminal k) tm.k₀ tm.k₁
      id id id rfl rfl n (encQMAFamilyAt F n) S₀ none
      tm.initialState.2 hi' hbase
      (haux₀ (ShiTMRepeatController.header false))
      (haux₀ (ShiTMRepeatController.header true))
      (haux₀ ShiTMRepeatController.scratch)
      (haux₀ ShiTMRepeatController.counter)
  have hstart' :
      (ShiTMSubroutine.run
        (ShiTMConstructiveIntegrated.machine p
          (liftedSource tm.m) tm.main
          (ShiTMRepeatConcrete.terminal k)
          tm.k₀ tm.k₁ id id id))^[
            2 * n + 3 +
              (ShiTMUnaryLogCost.work (n + 1) + n + 3)]
        (some ⟨some ShiTMConstructiveIntegrated.scan,
          (none, (true, tm.initialState.2)), S₀⟩) =
      some (ShiTMSubroutine.cfg
        ShiTMConstructiveIntegrated.controller
        (ShiTMRepeatController.loopInput tm.main tm.k₀
          (parity, tm.initialState.2)
          (ShiBQP.encNat n ++ encQMAFamilyAt F n)
          false n q)) := by
    have hheader :
        (List.replicate n true).map (id : Bool → tm.Γ tm.k₀) ++
          id false :: encQMAFamilyAt F n =
        ShiBQP.encNat n ++ encQMAFamilyAt F n := by
      change (List.replicate n true).map (id : Bool → Bool) ++
        false :: encQMAFamilyAt F n = _
      rw [List.map_id]
      simp [ShiBQP.encNat, List.append_assoc]
    exact hstart.trans (congrArg
      (fun raw : List (tm.Γ tm.k₀) =>
        some (ShiTMSubroutine.cfg ShiTMConstructiveIntegrated.controller
          (ShiTMRepeatController.loopInput tm.main tm.k₀
            (parity, tm.initialState.2) raw false n q))) hheader)
  obtain ⟨times, htimes, t, S', hloop, hout, hother, haux, hcost⟩ :=
    hk F n q false parity
  refine ⟨times, htimes, t, parity, S', ?_, ?_, hother,
    haux, hcost⟩
  · have hloop' :
        (ShiTMSubroutine.run
          (ShiTMRepeatController.machine
            (liftedSource tm.m) tm.main
            (ShiTMRepeatConcrete.terminal k)
            tm.k₀ tm.k₁ id id))^[t]
          (some (ShiTMRepeatController.loopInput
            tm.main tm.k₀
            (parity, tm.initialState.2)
            (ShiBQP.encNat n ++ encQMAFamilyAt F n)
            false n q)) =
          some ⟨none, (none, (parity, tm.initialState.2)), S'⟩ := by
        simpa [controllerMachine, tm] using hloop
    have hrun := ShiTMConstructiveIntegrated.startup_then_controller
      p (liftedSource tm.m) tm.main
      (ShiTMRepeatConcrete.terminal k) tm.k₀ tm.k₁
      id id id
      (2 * n + 3 +
        (ShiTMUnaryLogCost.work (n + 1) + n + 3)) t
      (some ⟨some ShiTMConstructiveIntegrated.scan,
        (none, (true, tm.initialState.2)), S₀⟩)
      (ShiTMRepeatController.loopInput tm.main tm.k₀
        (parity, tm.initialState.2)
        (ShiBQP.encNat n ++ encQMAFamilyAt F n)
        false n q)
      (⟨none, (none, (parity, tm.initialState.2)), S'⟩)
      hstart' hloop'
    exact hrun
  · have hq : q + 1 = ShiQMAConstructiveSchedule.rounds p n := by
      dsimp [q, ShiQMAConstructiveSchedule.rounds,
        ShiQMAConstructiveSchedule.exponentBudget]
    simpa [hq] using hout

end ShiTMConstructiveConcrete
