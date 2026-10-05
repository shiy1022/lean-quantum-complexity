import «AMPUNI-polynomial-fueled-assembly»
import «AMPUNI-clocked-cleanup-finite»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMTotalPolynomialClocked
variable (tm : Turing.FinTM2) (inputEquiv : Bool ≃ tm.Γ tm.k₀)
local instance : Fintype tm.K := tm.kFin
local instance : Fintype tm.Λ := tm.ΛFin
local instance : Fintype tm.σ := tm.σFin
abbrev clock := ShiTMClockedInterface.finiteMachine tm

def finiteMachine (d k : Nat) : Turing.FinTM2 where
  K := ShiTMFuel.Stack ⊕ ShiTMTypedTimeout.ClockK tm.K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl .input
  k₁ := .inr (.inl tm.k₁)
  Γ := ShiTMFuelFrame.Gam (G := ShiTMTypedTimeout.ClockGam tm.Γ)
  Λ := ShiTMPolynomialFueledAssembly.Label (B := (clock tm).Λ) d
  main := ShiTMPolynomialFueledAssembly.fuelLabel ShiTMPolynomialFuel.init
  ΛFin := inferInstance
  σ := Option Bool × (tm.σ × Bool)
  initialState := (none, (tm.initialState,false))
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := ShiTMPolynomialFueledAssembly.machine (.inl tm.k₀) (.inr ()) inputEquiv id d k
    (clock tm).m (clock tm).main

theorem initial_eq (d k : Nat) (xs : List Bool) :
    Turing.initList (finiteMachine tm inputEquiv d k) xs =
      ShiTMPolynomialFueledAssembly.initial (B := (clock tm).Λ)
        (G := ShiTMTypedTimeout.ClockGam tm.Γ) (tm.initialState,false) xs := by
  change (⟨some (ShiTMPolynomialFueledAssembly.fuelLabel ShiTMPolynomialFuel.init),
    (none,(tm.initialState,false)), _⟩ : Cfg _ _ _) =
      ⟨some (ShiTMPolynomialFueledAssembly.fuelLabel ShiTMPolynomialFuel.init),
        (none,(tm.initialState,false)), _⟩
  congr 1
  funext j
  cases j with
  | inl j => cases j <;> simp [finiteMachine] <;> rfl
  | inr j => simp [finiteMachine] <;> rfl

theorem transferred_eq (budget : Nat) (xs : List Bool) :
    ShiTMFuelTransfer.transferred (.inl tm.k₀) (.inr ()) inputEquiv id xs budget =
      (ShiTMClockedInterface.start tm budget (xs.map inputEquiv)).stk := by
  funext j
  cases j with
  | inl j =>
      by_cases hj : j = tm.k₀
      · subst j
        simp [ShiTMFuelTransfer.transferred, ShiTMClockedInterface.start,
          ShiTMClockedCleanup.startCfg, ShiTMSubroutine.cfg, ShiTMClockExit.cfg,
          ShiTMClockExit.finishCfg, ShiTMTypedTimeout.liftCfg, ShiTMTypedTimeout.liftStk,
          Turing.initList] <;> rfl
      · simp [ShiTMFuelTransfer.transferred, ShiTMClockedInterface.start,
          ShiTMClockedCleanup.startCfg, ShiTMSubroutine.cfg, ShiTMClockExit.cfg,
          ShiTMClockExit.finishCfg, ShiTMTypedTimeout.liftCfg, ShiTMTypedTimeout.liftStk,
          Turing.initList, hj]
  | inr u =>
      cases u
      simp [ShiTMFuelTransfer.transferred, ShiTMClockedInterface.start,
        ShiTMClockedCleanup.startCfg, ShiTMSubroutine.cfg, ShiTMClockExit.cfg,
        ShiTMClockExit.finishCfg, ShiTMTypedTimeout.liftCfg, ShiTMTypedTimeout.liftStk]

theorem final_eq (d k : Nat) (ys : List (tm.Γ tm.k₁)) :
    ShiTMSubroutine.cfg ShiTMPolynomialFueledAssembly.bodyLabel
      (ShiTMRightFrame.cfg (fun j : ShiTMFuel.Stack => ([] : List (ShiTMFuel.Gam j)))
        (none : Option Bool) (ShiTMClockedInterface.finish tm ys)) =
      Turing.haltList (finiteMachine tm inputEquiv d k) ys := by
  change (⟨none, (none,(tm.initialState,false)), _⟩ : Cfg _ _ _) =
    ⟨none, (none,(tm.initialState,false)), _⟩
  congr 1
  funext j
  cases j with
  | inl j => simp [finiteMachine, ShiTMSubroutine.cfg, ShiTMRightFrame.cfg, ShiTMStackFrame.extendStacks] <;> rfl
  | inr j =>
      by_cases hj : j = Sum.inl tm.k₁
      · subst j
        simp [finiteMachine, ShiTMSubroutine.cfg, ShiTMRightFrame.cfg, ShiTMStackFrame.extendStacks,
          ShiTMClockedInterface.finish, ShiTMClockedCleanup.haltCfg] <;> rfl
      · simp [finiteMachine, ShiTMSubroutine.cfg, ShiTMRightFrame.cfg, ShiTMStackFrame.extendStacks,
          ShiTMClockedInterface.finish, ShiTMClockedCleanup.haltCfg, hj] <;> rfl

/-- A supplied-fuel clocked run becomes a run from ordinary raw input,
including fuel construction and transfer, with canonical final cleanup. -/
theorem from_clocked_run (d k : Nat) (xs : List Bool) (ys : List (tm.Γ tm.k₁))
    (steps : Nat)
    (hr : (ShiTMClockedInterface.run tm)^[steps]
      (some (ShiTMClockedInterface.start tm (k*(xs.length+1)^(d+1)) (xs.map inputEquiv))) =
        some (ShiTMClockedInterface.finish tm ys)) :
    (ShiTMSubroutine.run (finiteMachine tm inputEquiv d k).m)^[ShiTMPolynomialFueledAssembly.prefixCost d k xs+steps]
      (some (Turing.initList (finiteMachine tm inputEquiv d k) xs)) =
        some (Turing.haltList (finiteMachine tm inputEquiv d k) ys) := by
  have hs : (⟨some (Sum.inl (ShiTMTypedTimeout.tick tm.main)), (tm.initialState,false),
      ShiTMFuelTransfer.transferred (.inl tm.k₀) (.inr ()) inputEquiv id xs (k*(xs.length+1)^(d+1))⟩ :
        Cfg (ShiTMTypedTimeout.ClockGam tm.Γ) (ShiTMClockedCleanup.Label (L := tm.Λ) tm.k₁)
          (tm.σ × Bool)) = ShiTMClockedInterface.start tm (k*(xs.length+1)^(d+1)) (xs.map inputEquiv) := by
    rw [transferred_eq]
    rfl
  have hr' : (ShiTMSubroutine.run (ShiTMClockedCleanup.machine tm.k₁ tm.initialState tm.m))^[steps]
      (some ⟨some (Sum.inl (ShiTMTypedTimeout.tick tm.main)), (tm.initialState,false),
        ShiTMFuelTransfer.transferred (.inl tm.k₀) (.inr ()) inputEquiv id xs (k*(xs.length+1)^(d+1))⟩) =
      some (ShiTMClockedInterface.finish tm ys) := by rw [hs]; exact hr
  have h := ShiTMPolynomialFueledAssembly.assemble (.inl tm.k₀) (.inr ()) inputEquiv id d k
    (ShiTMClockedCleanup.machine tm.k₁ tm.initialState tm.m)
    (Sum.inl (ShiTMTypedTimeout.tick tm.main)) (by simp) (tm.initialState,false) xs steps _ hr'
  rw [initial_eq, ← final_eq]
  exact h

end ShiTMTotalPolynomialClocked
