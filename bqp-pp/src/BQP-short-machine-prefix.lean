import «BQP-short-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BQPShortMachine
open Turing Turing.TM2

def inputStacks (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : ∀ k, List (tm.Γ k) :=
  (initList tm s).stk

@[simp] theorem inputStacks_at (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    inputStacks tm s tm.k₀ = s := by simp [inputStacks, initList]

@[simp] theorem inputStacks_update (tm : FinTM2) (s t : List (tm.Γ tm.k₀)) :
    Function.update (inputStacks tm s) tm.k₀ t = inputStacks tm t := by
  funext k
  by_cases hk : k = tm.k₀
  · subst k; simp [inputStacks, initList]
  · simp [inputStacks, initList, hk]

@[simp] theorem inputStacks_empty (tm : FinTM2) (k : tm.K) :
    inputStacks tm [] k = [] := by
  by_cases hk : k = tm.k₀
  · subst k; exact inputStacks_at tm []
  · simp [inputStacks, initList, hk]

theorem emptyStacks_output (tm : FinTM2) (a : tm.Γ tm.k₁) :
    Function.update (inputStacks tm []) tm.k₁ [a] = (haltList tm [a]).stk := by
  funext k
  by_cases hk : k = tm.k₁
  · subst k; simp [inputStacks, initList, haltList]
  · simp only [Function.update_of_ne hk, inputStacks_empty]
    simp [haltList, hk]

def inputCfg (tm : FinTM2) (l : Label tm) (v : State tm) (s : List (tm.Γ tm.k₀)) :
    Cfg tm.Γ (Label tm) (State tm) := ⟨some l, v, inputStacks tm s⟩

theorem start_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool)
    (v : State tm) (a : tm.Γ tm.k₀) (s : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)
      (some (inputCfg tm (start tm) v (a :: s))) =
    some (inputCfg tm (match ea a with | .inl b => second tm b | .inr _ => drain tm c₀)
      (v.1, some a) s) := by
  cases ha : ea a <;>
    simp [ShiTMSubroutine.run, step, inputCfg, start, program, stepAux, ha]

theorem start_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ : Bool) (v : State tm) :
    ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)
      (some (inputCfg tm (start tm) v [])) =
    some (inputCfg tm (drain tm c₀) (v.1, none) []) := by
  simp [ShiTMSubroutine.run, step, inputCfg, start, program, stepAux]

theorem second_left (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b d : Bool)
    (v : State tm) (s : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)
      (some (inputCfg tm (second tm b) v (ea.symm (.inl d) :: s))) =
    some (embed tm (initList tm (ea.symm (.inl b) :: ea.symm (.inl d) :: s))) := by
  change _ = some (inputCfg tm (.inr tm.main) (tm.initialState, none)
    (ea.symm (.inl b) :: ea.symm (.inl d) :: s))
  simp [ShiTMSubroutine.run, step, inputCfg, second, program, stepAux]

/-- Inspecting two instance symbols restores the entire input exactly before
delegation. This costs two transitions, independently of witness length. -/
theorem long_prefix (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b d : Bool) (s : List (tm.Γ tm.k₀)) :
    (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[2]
      (some (initList (machine tm ea eb c₀ c₁ c₂)
        (ea.symm (.inl b) :: ea.symm (.inl d) :: s))) =
    some (embed tm (initList tm (ea.symm (.inl b) :: ea.symm (.inl d) :: s))) := by
  have hs := start_cons tm ea eb c₀ c₁ c₂ (tm.initialState, none)
    (ea.symm (.inl b)) (ea.symm (.inl d) :: s)
  simp only [Equiv.apply_symm_apply] at hs
  exact (congrArg (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)) hs).trans
    (second_left tm ea eb c₀ c₁ c₂ b d (tm.initialState, some (ea.symm (.inl b))) s)

theorem drain_cons (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b : Bool)
    (v : State tm) (a : tm.Γ tm.k₀) (s : List (tm.Γ tm.k₀)) :
    ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)
      (some (inputCfg tm (drain tm b) v (a :: s))) =
    some (inputCfg tm (drain tm b) (v.1, some a) s) := by
  simp [ShiTMSubroutine.run, step, inputCfg, drain, program, stepAux]

theorem drain_nil (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b : Bool) (v : State tm) :
    ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂)
      (some (inputCfg tm (drain tm b) v [])) =
    some (haltList (machine tm ea eb c₀ c₁ c₂) [eb.symm b]) := by
  simp [ShiTMSubroutine.run, step, inputCfg, drain, program, stepAux,
    emptyStacks_output]
  rfl

theorem drain_run (tm : FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)
    (eb : tm.Γ tm.k₁ ≃ Bool) (c₀ c₁ c₂ b : Bool)
    (s : List (tm.Γ tm.k₀)) (v : State tm) :
    (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[s.length + 1]
      (some (inputCfg tm (drain tm b) v s)) =
    some (haltList (machine tm ea eb c₀ c₁ c₂) [eb.symm b]) := by
  induction s generalizing v with
  | nil => exact drain_nil tm ea eb c₀ c₁ c₂ b v
  | cons a s ih =>
      change (ShiTMSubroutine.run (program tm ea eb c₀ c₁ c₂))^[s.length + 1 + 1] _ = _
      rw [Function.iterate_succ_apply, drain_cons]
      exact ih (v.1, some a)

end BQPShortMachine
