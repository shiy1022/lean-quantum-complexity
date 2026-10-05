import «AMPUNI-fueled-assembly»
import «AMPUNI-repeat-clocked-cleanup»
import «AMPUNI-total-clocked-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section

namespace ShiTMRepeatFueled
variable (tm : Turing.FinTM2) (inputEquiv : Bool ≃ tm.Γ tm.k₀)
local instance : Fintype tm.K := tm.kFin
local instance : Fintype tm.Λ := tm.ΛFin
local instance : Fintype tm.σ := tm.σFin

abbrev bodyLabel :=
  ShiTMRepeatClocked.Label (L := tm.Λ) tm.k₁

/-- A finite one-round machine whose successful output remains at an active handoff. -/
def finiteMachine (k : Nat) : Turing.FinTM2 where
  K := ShiTMFuel.Stack ⊕ ShiTMTypedTimeout.ClockK tm.K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl .input
  k₁ := .inr (.inl tm.k₁)
  Γ := ShiTMFuelFrame.Gam (G := ShiTMTypedTimeout.ClockGam tm.Γ)
  Λ := ShiTMFueledAssembly.Label (B := bodyLabel tm)
  main := ShiTMFueledAssembly.fuelLabel .init
  ΛFin := inferInstance
  σ := Option Bool × (tm.σ × Bool)
  initialState := (none, (tm.initialState, false))
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := ShiTMFueledAssembly.machine (.inl tm.k₀) (.inr ()) inputEquiv id k
    (ShiTMRepeatClocked.machine tm.k₁ tm.initialState tm.m)
    (.inl (ShiTMTypedTimeout.tick tm.main))

def activeFinish (k : Nat) (ys : List (tm.Γ tm.k₁)) :
    (finiteMachine tm inputEquiv k).Cfg :=
  ShiTMSubroutine.cfg ShiTMFueledAssembly.bodyLabel
    (ShiTMRightFrame.cfg (fun j : ShiTMFuel.Stack => ([] : List (ShiTMFuel.Gam j)))
      (none : Option Bool)
      (ShiTMRepeatClocked.activeFinish tm.k₁ tm.initialState ys))

theorem initial_eq (k : Nat) (xs : List Bool) :
    Turing.initList (finiteMachine tm inputEquiv k) xs =
      ShiTMFueledAssembly.initial
        (B := bodyLabel tm)
        (G := ShiTMTypedTimeout.ClockGam tm.Γ)
        (tm.initialState, false) xs := by
  change (⟨some (ShiTMFueledAssembly.fuelLabel ShiTMFuel.Label.init),
    (none, (tm.initialState, false)), _⟩ : Cfg _ _ _) =
      ⟨some (ShiTMFueledAssembly.fuelLabel ShiTMFuel.Label.init),
        (none, (tm.initialState, false)), _⟩
  congr 1
  funext j
  cases j with
  | inl j => cases j <;> simp [finiteMachine] <;> rfl
  | inr j => simp [finiteMachine] <;> rfl

/-- Lift one clocked valid run through fuel construction and transfer. -/
theorem from_clocked_run (k : Nat) (xs : List Bool)
    (ys : List (tm.Γ tm.k₁)) (steps : Nat)
    (hr : (ShiTMRepeatClocked.run tm.k₁ tm.initialState tm.m)^[steps]
      (some (ShiTMRepeatClocked.startCfg tm.k₁
        (List.replicate (k * (xs.length + 1) ^ 2) true)
        (Turing.initList tm (xs.map inputEquiv)))) =
      some (ShiTMRepeatClocked.activeFinish tm.k₁ tm.initialState ys)) :
    (ShiTMSubroutine.run (finiteMachine tm inputEquiv k).m)^[
      ShiTMFueledAssembly.prefixCost k xs + steps]
      (some (Turing.initList (finiteMachine tm inputEquiv k) xs)) =
        some (activeFinish tm inputEquiv k ys) := by
  have hs :
      (⟨some (Sum.inl (ShiTMTypedTimeout.tick tm.main)),
        (tm.initialState, false),
        ShiTMFuelTransfer.transferred (.inl tm.k₀) (.inr ())
          inputEquiv id xs (k * (xs.length + 1) ^ 2)⟩ :
          Cfg (ShiTMTypedTimeout.ClockGam tm.Γ)
            (bodyLabel tm) (tm.σ × Bool)) =
        ShiTMRepeatClocked.startCfg tm.k₁
          (List.replicate (k * (xs.length + 1) ^ 2) true)
          (Turing.initList tm (xs.map inputEquiv)) := by
    rw [ShiTMTotalClocked.transferred_eq]
    rfl
  have hr' :
      (ShiTMSubroutine.run
        (ShiTMRepeatClocked.machine tm.k₁ tm.initialState tm.m))^[steps]
        (some ⟨some (Sum.inl (ShiTMTypedTimeout.tick tm.main)),
          (tm.initialState, false),
          ShiTMFuelTransfer.transferred (.inl tm.k₀) (.inr ())
            inputEquiv id xs (k * (xs.length + 1) ^ 2)⟩) =
          some (ShiTMRepeatClocked.activeFinish tm.k₁ tm.initialState ys) := by
    rw [hs]
    exact hr
  have h := ShiTMFueledAssembly.assemble
    (.inl tm.k₀) (.inr ()) inputEquiv id k
    (ShiTMRepeatClocked.machine tm.k₁ tm.initialState tm.m)
    (Sum.inl (ShiTMTypedTimeout.tick tm.main))
    (by simp) (tm.initialState, false) xs steps _ hr'
  rw [initial_eq]
  exact h

end ShiTMRepeatFueled
