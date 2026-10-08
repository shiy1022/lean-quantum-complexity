import ReversibleWorkspaceOffsets
import ReversibleGeneratorPrelude

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def resourceLayoutOperations (tm : Turing.FinTM2) : List (GeneratorOperation WorkspaceRegister) := by
  classical
  let k := 10 + Fintype.card (Option (MachineSymbol tm)) * 7
  exact [.affine ⟨1, 2, 0, machinePushBound tm⟩, .affine ⟨0, 2, 1, 1⟩,
    .affine ⟨2, 3, Fintype.card (Option tm.Λ) + Fintype.card tm.σ,
      Fintype.card tm.K * Fintype.card (Option (MachineSymbol tm))⟩,
    .affine ⟨2, 4, k + 2, k⟩]

def resourceBudgetState (n budget : Nat) : WorkspaceRegister → Nat :=
  fun r => if r = 0 then n else if r = 1 then budget else 0

theorem resourceLayout_valid (tm : Turing.FinTM2) :
    ∀ op ∈ resourceLayoutOperations tm, op.Valid 6 5 := by
  classical
  simp [resourceLayoutOperations, GeneratorOperation.Valid, AffineAtom.Valid]

theorem resourceLayout_result (tm : Turing.FinTM2) (n budget : Nat) :
    operationResult (resourceLayoutOperations tm) (resourceBudgetState n budget) =
      workspaceInitial tm n budget := by
  classical
  funext r
  fin_cases r <;> simp [operationResult, resourceLayoutOperations, GeneratorOperation.apply,
    AffineAtom.apply, resourceBudgetState, workspaceInitial, configurationWidth, extractionBitBound]
  all_goals ring

theorem resourceLayout_clock_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      operationSteps (resourceLayoutOperations tm) (resourceBudgetState n (time.eval n)) = p.eval n := by
  let sizes : WorkspaceRegister → Polynomial Nat :=
    fun r => if r = 0 then Polynomial.X else if r = 1 then time else 0
  refine ⟨operationClock (resourceLayoutOperations tm) sizes, ?_⟩
  intro n
  rw [operationClock_eval]
  congr 1
  funext r
  by_cases h₀ : r = 0 <;> by_cases h₁ : r = 1 <;> simp [sizes, resourceBudgetState, h₀, h₁]

abbrev ResourcePreludeLabels (tm : Turing.FinTM2) (c d : Nat) (L : Type) :=
  InitializedBudgetLabel c d (GeneratorOperationLabels (resourceLayoutOperations tm)
    (GeneratorOperationLabels (workspaceOperations tm) L))

noncomputable def resourcePreludeCode {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr WorkspaceRegister L) (stop : L) :
    ResourcePreludeLabels tm c d L → CounterInstr WorkspaceRegister (ResourcePreludeLabels tm c d L) :=
  let workspace := operationCode (workspaceOperations tm) caller 6 5 stop
  let layout := operationCode (resourceLayoutOperations tm) workspace 6 5
    (operationEntry (workspaceOperations tm) stop)
  initializedBudgetCode layout c d 1 0 2 5
    (operationEntry (resourceLayoutOperations tm) (operationEntry (workspaceOperations tm) stop))

/-- All resource metadata is obtained by one finite program starting with only raw length. -/
theorem resourcePreludeCode_run {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr WorkspaceRegister L) (stop : L) (n : Nat) (ys : List Bool) :
    CounterRun (resourcePreludeCode tm c d caller stop)
      ⟨some (.inl ()), resourceBudgetState n 0, ys⟩
      ((powerWork (n + c) d + 2 * d + 2 * c + 1 +
        operationSteps (resourceLayoutOperations tm) (resourceBudgetState n ((n + c) ^ d))) +
        operationSteps (workspaceOperations tm) (workspaceInitial tm n ((n + c) ^ d)))
      ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm)
        (operationExit (workspaceOperations tm) stop))),
        operationResult (workspaceOperations tm) (workspaceInitial tm n ((n + c) ^ d)), ys⟩ := by
  let workspace := operationCode (workspaceOperations tm) caller 6 5 stop
  let layStop := operationEntry (workspaceOperations tm) stop
  let layout := operationCode (resourceLayoutOperations tm) workspace 6 5 layStop
  let budStop := operationEntry (resourceLayoutOperations tm) layStop
  let outer := resourcePreludeCode tm c d caller stop
  let base : CounterCfg WorkspaceRegister (ResourcePreludeLabels tm c d L) := ⟨none, fun _ => 0, ys⟩
  have hb := initializedBudgetCode_run layout c d (1 : WorkspaceRegister) 0 2 5 budStop
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) base n
  have hi : multiplyState base 1 0 2 5 0 n 0 (.inl ()) =
      (⟨some (.inl ()), resourceBudgetState n 0, ys⟩ : CounterCfg WorkspaceRegister (ResourcePreludeLabels tm c d L)) := by
    apply CounterCfg.ext
    · rfl
    · funext r; fin_cases r <;> simp [multiplyState, copyState, withCounter, base, resourceBudgetState]
    · rfl
  have ho : multiplyState base 1 0 2 5 ((n + c) ^ d) n 0 (initializedBudgetEmbed budStop) =
      (⟨some (initializedBudgetEmbed budStop), resourceBudgetState n ((n + c) ^ d), ys⟩ :
        CounterCfg WorkspaceRegister (ResourcePreludeLabels tm c d L)) := by
    apply CounterCfg.ext
    · rfl
    · funext r; fin_cases r <;> simp [multiplyState, copyState, withCounter, base, resourceBudgetState]
    · rfl
  change CounterRun outer (multiplyState base 1 0 2 5 0 n 0 (.inl ()))
    (powerWork (n + c) d + 2 * d + 2 * c + 1)
    (multiplyState base 1 0 2 5 ((n + c) ^ d) n 0 (initializedBudgetEmbed budStop)) at hb
  rw [hi, ho] at hb
  have hl := operationCode_run (resourceLayoutOperations tm) workspace 6 5 layStop
    (resourceLayout_valid tm) (by decide) (resourceBudgetState n ((n + c) ^ d))
    (by simp [resourceBudgetState]) (by simp [resourceBudgetState]) ys
  rw [resourceLayout_result] at hl
  have hl' := CounterRun.relabel layout outer initializedBudgetEmbed
    (initializedBudgetCode_embed layout c d 1 0 2 5 budStop) hl
  have hw := workspaceOffsetsCode_run tm caller stop n ((n + c) ^ d) ys
  have hw' := CounterRun.relabel workspace layout (operationExit (resourceLayoutOperations tm))
    (operationCode_embed (resourceLayoutOperations tm) workspace 6 5 layStop) hw
  have hw'' := CounterRun.relabel layout outer initializedBudgetEmbed
    (initializedBudgetCode_embed layout c d 1 0 2 5 budStop) hw'
  change CounterRun outer
    ⟨some (initializedBudgetEmbed budStop), resourceBudgetState n ((n + c) ^ d), ys⟩
    (operationSteps (resourceLayoutOperations tm) (resourceBudgetState n ((n + c) ^ d)))
    ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm) layStop)),
      workspaceInitial tm n ((n + c) ^ d), ys⟩ at hl'
  change CounterRun outer
    ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm) layStop)),
      workspaceInitial tm n ((n + c) ^ d), ys⟩
    (operationSteps (workspaceOperations tm) (workspaceInitial tm n ((n + c) ^ d)))
    ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm)
      (operationExit (workspaceOperations tm) stop))),
      operationResult (workspaceOperations tm) (workspaceInitial tm n ((n + c) ^ d)), ys⟩ at hw''
  exact CounterRun.trans outer (CounterRun.trans outer hb hl') hw''

theorem resourcePreludeCode_clock_polynomial (tm : Turing.FinTM2) (c d : Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      (powerWork (n + c) d + 2 * d + 2 * c + 1 +
        operationSteps (resourceLayoutOperations tm) (resourceBudgetState n ((n + c) ^ d))) +
        operationSteps (workspaceOperations tm) (workspaceInitial tm n ((n + c) ^ d)) = p.eval n := by
  let time : Polynomial Nat := (Polynomial.X + Polynomial.C c) ^ d
  obtain ⟨b, hb⟩ := budgetCode_clock_polynomial c d
  obtain ⟨l, hl⟩ := resourceLayout_clock_polynomial tm time
  obtain ⟨w, hw⟩ := workspaceOffsetsCode_clock_polynomial tm time
  refine ⟨(b + Polynomial.C 1 + l) + w, ?_⟩
  intro n
  have ht : time.eval n = (n + c) ^ d := by simp [time]
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  rw [← hb, ← hl, ← hw, ht]

end ShiReversibleGenerator
