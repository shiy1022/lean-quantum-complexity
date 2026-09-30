import «AMPUNI-scaled-log-run»
import «AMPUNI-constructive-schedule»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2 ShiTMUnaryLog
namespace ShiTMScaledLog

def finiteMachine (copies offset : Nat) : Turing.FinTM2 where
  K := Stack
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .a
  k₁ := .counter
  Γ := Gam
  Λ := Label
  main := .scan false
  ΛFin := inferInstance
  σ := State
  initialState := (none, true)
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine copies offset

theorem initial_eq (copies offset n : Nat) :
    Turing.initList (finiteMachine copies offset)
      (List.replicate n true) =
    cfg (.scan false) false none true (List.replicate n true) [] [] := by
  change (⟨some (Label.scan false), (none, true), _⟩ :
    Cfg Gam Label State) =
      ⟨some (Label.scan false), (none, true), _⟩
  congr 1
  funext j
  cases j <;> simp [finiteMachine, storeFn] <;> rfl

theorem done_step (copies offset : Nat) (direction parity : Bool)
    (ctr : List Bool) :
    run copies offset
      (some (cfg .done direction none parity [] [] ctr)) =
      some (⟨none, (none, true),
        storeFn direction [] []
          (List.replicate offset true ++ ctr)⟩ :
          Cfg Gam Label State) := by
  simp [run, ShiTMSubroutine.run, cfg, machine, step, stepAux]
  rw [stepAux_pushCounter]
  simp [stepAux]

theorem halted_eq (copies offset : Nat) (direction : Bool)
    (ctr : List Bool) :
    (⟨none, (none, true), storeFn direction [] [] ctr⟩ :
      Cfg Gam Label State) =
      Turing.haltList (finiteMachine copies offset) ctr := by
  congr 1
  funext j
  cases direction <;> cases j <;>
    simp [finiteMachine, storeFn] <;> rfl

/-- The finite machine computes `offset + copies * log₂ n` unary counter
tokens from actual unary input, in linear time. -/
theorem counter_from_init (copies offset n : Nat) :
    ∃ t : Nat,
      (ShiTMSubroutine.run (finiteMachine copies offset).m)^[t]
        (some (Turing.initList (finiteMachine copies offset)
          (List.replicate n true))) =
        some (Turing.haltList (finiteMachine copies offset)
          (List.replicate
            (offset + copies * Nat.log 2 n) true)) ∧
      t ≤ 4 * n + 5 := by
  obtain ⟨direction, parity, hr⟩ :=
    full_run copies offset n false none []
  refine ⟨ShiTMUnaryLogCost.work n + 1, ?_, ?_⟩
  · change (run copies offset)^[ShiTMUnaryLogCost.work n + 1]
      (some (Turing.initList (finiteMachine copies offset)
        (List.replicate n true))) =
        some (Turing.haltList (finiteMachine copies offset)
          (List.replicate (offset + copies * Nat.log 2 n) true))
    rw [initial_eq,
      show ShiTMUnaryLogCost.work n + 1 =
        1 + ShiTMUnaryLogCost.work n by omega,
      Function.iterate_add_apply, hr]
    simp only [Function.iterate_one]
    rw [done_step]
    have hc :
        List.replicate offset true ++
          (List.replicate (copies * Nat.log 2 n) true ++ []) =
        List.replicate (offset + copies * Nat.log 2 n) true := by
      rw [List.replicate_add]
      simp
    rw [hc, halted_eq]
    rfl
  · have h := ShiTMUnaryLogCost.work_le_linear n
    omega

def scheduleOffset (p : Polynomial ℕ) : ℕ :=
  Nat.log 2 (p.eval 1 + 1) + p.natDegree + 3

theorem schedule_counter_from_unary (p : Polynomial ℕ) (n : ℕ) :
    ∃ t : Nat,
      (ShiTMSubroutine.run
        (finiteMachine p.natDegree (scheduleOffset p)).m)^[t]
        (some (Turing.initList
          (finiteMachine p.natDegree (scheduleOffset p))
          (List.replicate (n + 1) true))) =
        some (Turing.haltList
          (finiteMachine p.natDegree (scheduleOffset p))
          (List.replicate
            (ShiQMAConstructiveSchedule.rounds p n - 1) true)) ∧
      t ≤ 4 * (n + 1) + 5 := by
  have hc : scheduleOffset p +
      p.natDegree * Nat.log 2 (n + 1) =
      ShiQMAConstructiveSchedule.rounds p n - 1 := by
    dsimp [scheduleOffset, ShiQMAConstructiveSchedule.rounds,
      ShiQMAConstructiveSchedule.exponentBudget]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  simpa only [hc] using
    counter_from_init p.natDegree (scheduleOffset p) (n + 1)

end ShiTMScaledLog
