import «AMPUNI-clocked-cleanup-interface»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMClockedInterface
variable (tm : Turing.FinTM2)
local instance : Fintype tm.K := tm.kFin
local instance : Fintype tm.Λ := tm.ΛFin
local instance : Fintype tm.σ := tm.σFin

/-- The clock and canonical cleanup preserve finiteness of the source
machine. A fuel-generating entry stage is still needed for ordinary input. -/
def finiteMachine : Turing.FinTM2 where
  K := ShiTMTypedTimeout.ClockK tm.K
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl tm.k₀
  k₁ := .inl tm.k₁
  Γ := ShiTMTypedTimeout.ClockGam tm.Γ
  Λ := ShiTMClockedCleanup.Label (L := tm.Λ) tm.k₁
  main := .inl (ShiTMTypedTimeout.tick tm.main)
  ΛFin := inferInstance
  σ := tm.σ × Bool
  initialState := (tm.initialState, false)
  σFin := inferInstance
  Γk₀Fin := tm.Γk₀Fin
  m := ShiTMClockedCleanup.machine tm.k₁ tm.initialState tm.m

theorem finish_eq_haltList (ys : List (tm.Γ tm.k₁)) :
    finish tm ys = Turing.haltList (finiteMachine tm) ys := by
  change (⟨none, (tm.initialState, false), _⟩ : Cfg _ _ _) =
    ⟨none, (tm.initialState, false), _⟩
  congr 1
  funext k
  by_cases hk : k = Sum.inl tm.k₁
  · subst k
    simp [finiteMachine]
    rfl
  · simp [finiteMachine, hk]

end ShiTMClockedInterface
