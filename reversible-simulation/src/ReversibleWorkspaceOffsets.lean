import ReversibleMixedArithmetic
import ReversiblePaddedMachine

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

abbrev WorkspaceRegister := Fin 16

/-- Metadata registers from the budget/layout prelude; every new work counter is zero. -/
noncomputable def workspaceInitial (tm : Turing.FinTM2) (n budget : Nat) : WorkspaceRegister → Nat :=
  let cap := n + budget * machinePushBound tm + 1
  fun r => if r = 0 then n else if r = 1 then budget else if r = 2 then cap else
    if r = 3 then configurationWidth tm cap else if r = 4 then extractionBitBound tm cap + 1 else 0

/-- Fixed control for exact prepared/output/workspace offsets. Only counters carry n-dependent data. -/
noncomputable def workspaceOperations (tm : Turing.FinTM2) : List (GeneratorOperation WorkspaceRegister) :=
  [.affine ⟨3, 7, 0, 18⟩,
   .affine ⟨3, 8, 0, tickSizeBound tm + 1⟩,
   .product ⟨1, 8, 7⟩,
   .affine ⟨7, 11, 0, 1⟩,
   .affine ⟨0, 11, 0, 1⟩,
   .affine ⟨2, 9, 1, 2⟩,
   .product ⟨9, 4, 7⟩,
   .affine ⟨7, 10, 0, 1⟩,
   .affine ⟨0, 10, 0, 1⟩]

theorem workspaceOperations_valid (tm : Turing.FinTM2) :
    ∀ op ∈ workspaceOperations tm, op.Valid 6 5 := by
  simp [workspaceOperations, GeneratorOperation.Valid, AffineAtom.Valid]

theorem workspaceResult_workspace (tm : Turing.FinTM2) (n budget : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n budget) 7 =
      paddedMachineWorkspace tm n budget := by
  simp [operationResult, workspaceOperations, GeneratorOperation.apply, AffineAtom.apply,
    workspaceInitial, paddedMachineWorkspace]
  ring

theorem workspaceResult_prepared (tm : Turing.FinTM2) (n budget : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n budget) 11 =
      n + configurationWidth tm (n + budget * machinePushBound tm + 1) * 18 +
        budget * (configurationWidth tm (n + budget * machinePushBound tm + 1) * (tickSizeBound tm + 1)) := by
  simp [operationResult, workspaceOperations, GeneratorOperation.apply, AffineAtom.apply, workspaceInitial]
  ring

theorem workspaceResult_output (tm : Turing.FinTM2) (n budget : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n budget) 10 =
      n + paddedMachineWorkspace tm n budget := by
  simp [operationResult, workspaceOperations, GeneratorOperation.apply, AffineAtom.apply,
    workspaceInitial, paddedMachineWorkspace]
  ring

theorem workspaceResult_buffer (tm : Turing.FinTM2) (n budget : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n budget) 6 = 0 := by
  simp [operationResult, workspaceOperations, GeneratorOperation.apply, AffineAtom.apply, workspaceInitial]

theorem workspaceResult_scratch (tm : Turing.FinTM2) (n budget : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n budget) 5 = 0 := by
  simp [operationResult, workspaceOperations, GeneratorOperation.apply, AffineAtom.apply, workspaceInitial]

/-- Actual finite-program computation of the exact semantic offsets, preserving emitted output. -/
theorem workspaceOffsetsCode_run {L : Type} (tm : Turing.FinTM2)
    (caller : L → CounterInstr WorkspaceRegister L) (stop : L) (n budget : Nat) (ys : List Bool) :
    CounterRun (operationCode (workspaceOperations tm) caller 6 5 stop)
      ⟨some (operationEntry (workspaceOperations tm) stop), workspaceInitial tm n budget, ys⟩
      (operationSteps (workspaceOperations tm) (workspaceInitial tm n budget))
      ⟨some (operationExit (workspaceOperations tm) stop),
        operationResult (workspaceOperations tm) (workspaceInitial tm n budget), ys⟩ :=
  operationCode_run _ caller 6 5 stop (workspaceOperations_valid tm) (by decide) _
    (by simp [workspaceInitial]) (by simp [workspaceInitial]) ys

theorem workspaceOffsetsCode_clock_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      operationSteps (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) = p.eval n := by
  obtain ⟨width, hw⟩ := clockedConfigurationWidth_polynomial tm time
  let cap : Polynomial Nat := Polynomial.X + time * Polynomial.C (machinePushBound tm) + Polynomial.C 1
  classical
  let stride : Polynomial Nat := Polynomial.C 2 + (cap + Polynomial.C 1) *
    Polynomial.C (10 + Fintype.card (Option (MachineSymbol tm)) * 7)
  let sizes : WorkspaceRegister → Polynomial Nat := fun r => if r = 0 then Polynomial.X else
    if r = 1 then time else if r = 2 then cap else if r = 3 then width else if r = 4 then stride else 0
  refine ⟨operationClock (workspaceOperations tm) sizes, ?_⟩
  intro n
  rw [operationClock_eval]
  congr 1
  funext r
  by_cases h₀ : r = 0 <;> by_cases h₁ : r = 1 <;> by_cases h₂ : r = 2 <;>
    by_cases h₃ : r = 3 <;> by_cases h₄ : r = 4
  all_goals simp [sizes, workspaceInitial, cap, stride, extractionBitBound, hw n, h₀, h₁, h₂, h₃, h₄]
  all_goals omega

end ShiReversibleGenerator
