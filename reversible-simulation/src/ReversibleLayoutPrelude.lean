import ReversibleArithmeticSequence
import ReversibleMachineExtraction

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Raw length, budget, capacity, configuration width, extraction stride, scratch. -/
abbrev LayoutRegister := Fin 6

def layoutInitial (n budget : Nat) : LayoutRegister → Nat :=
  fun r => if r = 0 then n else if r = 1 then budget else 0

/-- This fixed template reads the runtime budget; its control never depends on n. -/
noncomputable def layoutAtoms (tm : Turing.FinTM2) : List (AffineAtom LayoutRegister) := by
  classical
  let k := 10 + Fintype.card (Option (MachineSymbol tm)) * 7
  exact [⟨1, 2, 0, machinePushBound tm⟩, ⟨0, 2, 1, 1⟩,
    ⟨2, 3, Fintype.card (Option tm.Λ) + Fintype.card tm.σ,
      Fintype.card tm.K * Fintype.card (Option (MachineSymbol tm))⟩,
    ⟨2, 4, k + 2, k⟩]

theorem layoutAtoms_valid (tm : Turing.FinTM2) :
    ∀ a ∈ layoutAtoms tm, a.Valid 5 := by
  classical
  simp [layoutAtoms, AffineAtom.Valid]

theorem layoutResult_raw (tm : Turing.FinTM2) (n budget : Nat) :
    arithmeticResult (layoutAtoms tm) (layoutInitial n budget) 0 = n := by
  classical
  simp [arithmeticResult, layoutAtoms, AffineAtom.apply, layoutInitial]

theorem layoutResult_budget (tm : Turing.FinTM2) (n budget : Nat) :
    arithmeticResult (layoutAtoms tm) (layoutInitial n budget) 1 = budget := by
  classical
  simp [arithmeticResult, layoutAtoms, AffineAtom.apply, layoutInitial]

theorem layoutResult_capacity (tm : Turing.FinTM2) (n budget : Nat) :
    arithmeticResult (layoutAtoms tm) (layoutInitial n budget) 2 =
      n + budget * machinePushBound tm + 1 := by
  classical
  simp [arithmeticResult, layoutAtoms, AffineAtom.apply, layoutInitial]
  ring

theorem layoutResult_width (tm : Turing.FinTM2) (n budget : Nat) :
    arithmeticResult (layoutAtoms tm) (layoutInitial n budget) 3 =
      configurationWidth tm (n + budget * machinePushBound tm + 1) := by
  classical
  simp [arithmeticResult, layoutAtoms, AffineAtom.apply, layoutInitial, configurationWidth]
  ring

theorem layoutResult_stride (tm : Turing.FinTM2) (n budget : Nat) :
    arithmeticResult (layoutAtoms tm) (layoutInitial n budget) 4 =
      extractionBitBound tm (n + budget * machinePushBound tm + 1) + 1 := by
  classical
  simp [arithmeticResult, layoutAtoms, AffineAtom.apply, layoutInitial, extractionBitBound]
  ring

theorem layoutResult_scratch (tm : Turing.FinTM2) (n budget : Nat) :
    arithmeticResult (layoutAtoms tm) (layoutInitial n budget) 5 = 0 := by
  classical
  simp [arithmeticResult, layoutAtoms, AffineAtom.apply, layoutInitial]

/-- Exact run of the concrete layout fragment, with arbitrary output and continuation. -/
theorem layoutCode_run {L : Type} (tm : Turing.FinTM2)
    (caller : L → CounterInstr LayoutRegister L) (stop : L) (n budget : Nat) (ys : List Bool) :
    CounterRun (arithmeticCode (layoutAtoms tm) caller 5 stop)
      ⟨some (arithmeticEntry (layoutAtoms tm) stop), layoutInitial n budget, ys⟩
      (arithmeticSteps (layoutAtoms tm) (layoutInitial n budget))
      ⟨some (arithmeticExit (layoutAtoms tm) stop),
        arithmeticResult (layoutAtoms tm) (layoutInitial n budget), ys⟩ :=
  arithmeticCode_run _ caller 5 stop (layoutAtoms_valid tm) _ (by simp [layoutInitial]) ys

theorem layoutCode_clock_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ p : Polynomial Nat, ∀ n,
      arithmeticSteps (layoutAtoms tm) (layoutInitial n (time.eval n)) = p.eval n := by
  let sizes : LayoutRegister → Polynomial Nat :=
    fun r => if r = 0 then Polynomial.X else if r = 1 then time else 0
  refine ⟨arithmeticClock (layoutAtoms tm) sizes, ?_⟩
  intro n
  rw [arithmeticClock_eval]
  congr 1
  funext r
  by_cases h : r = 0 <;> by_cases h₁ : r = 1 <;> simp [sizes, layoutInitial, h, h₁]

end ShiReversibleGenerator
