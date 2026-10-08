import ReversibleCellAddressArithmetic
import ReversibleFinalCleanup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

theorem arithmeticCode_embed_fixed (atoms : List (AffineAtom R)) (caller : L → CounterInstr R L)
    (tmp : R) (stop l : L) :
    arithmeticCode atoms caller tmp stop (arithmeticExit atoms l) =
      (caller l).relabel (arithmeticExit atoms) := by
  induction atoms with
  | nil =>
    change caller l = (caller l).relabel (fun x => x)
    cases caller l <;> rfl
  | cons a atoms ih =>
    change ((arithmeticCode atoms caller tmp stop (arithmeticExit atoms l)).relabel Sum.inr).relabel Sum.inr = _
    rw [ih]
    cases caller l <;> rfl

abbrev CellAddressBindingLabels (input capacity index target : R) (offset rank stride : Nat) (L : Type) :=
  ClearLabel (ArithmeticLabels (cellAddressAtoms input capacity index target offset rank stride) (ClearLabel L))

def cellAddressBindingExit (input capacity index target : R) (offset rank stride : Nat) (l : L) :
    CellAddressBindingLabels input capacity index target offset rank stride L :=
  .inr (arithmeticExit (cellAddressAtoms input capacity index target offset rank stride) (.inr l))

def cellAddressBindingCode (caller : L → CounterInstr R L) (input capacity index target tmp : R)
    (offset rank stride : Nat) (stop : L) :
    CellAddressBindingLabels input capacity index target offset rank stride L →
      CounterInstr R (CellAddressBindingLabels input capacity index target offset rank stride L) :=
  let atoms := cellAddressAtoms input capacity index target offset rank stride
  let suffix := clearCode index caller stop
  let arith := arithmeticCode atoms suffix tmp (.inl 0)
  clearCode target arith (arithmeticEntry atoms (.inl 0))

def cellAddressBindingSteps (input capacity index target : R) (offset rank stride : Nat) (cs : R → Nat) : Nat :=
  ((2 * cs target + 1) +
    arithmeticSteps (cellAddressAtoms input capacity index target offset rank stride) (Function.update cs target 0)) +
    (2 * cs index + 1)

def cellAddressBindingCounters (input capacity index target : R) (offset rank stride : Nat) (cs : R → Nat) : R → Nat :=
  Function.update (Function.update cs target
    (cs input + offset + (rank * stride) * cs capacity + stride * cs index)) index 0

/-- Actual affine binding clears the old slot and consumes the temporary query index. -/
theorem cellAddressBindingCode_run (caller : L → CounterInstr R L) (input capacity index target tmp : R)
    (offset rank stride : Nat) (stop : L)
    (hit : input ≠ target) (hct : capacity ≠ target) (hjt : index ≠ target)
    (hix : input ≠ tmp) (hcx : capacity ≠ tmp) (hjx : index ≠ tmp) (htx : target ≠ tmp)
    (cs : R → Nat) (hx : cs tmp = 0) (ys : List Bool) :
    CounterRun (cellAddressBindingCode caller input capacity index target tmp offset rank stride stop)
      ⟨some (.inl 0), cs, ys⟩ (cellAddressBindingSteps input capacity index target offset rank stride cs)
      ⟨some (cellAddressBindingExit input capacity index target offset rank stride stop),
        cellAddressBindingCounters input capacity index target offset rank stride cs, ys⟩ := by
  let atoms := cellAddressAtoms input capacity index target offset rank stride
  let suffix := clearCode index caller stop
  let arith := arithmeticCode atoms suffix tmp (.inl 0)
  let code := cellAddressBindingCode caller input capacity index target tmp offset rank stride stop
  let cs₀ := Function.update cs target 0
  let addressed := arithmeticResult atoms cs₀
  have hc := clearCode_run target arith (arithmeticEntry atoms (.inl 0)) cs ys
  have ha := arithmeticCode_run atoms suffix tmp (.inl 0)
    (cellAddressAtoms_valid input capacity index target tmp offset rank stride hit hct hjt hix hcx hjx htx)
    cs₀ (by simp [cs₀, Ne.symm htx, hx]) ys
  have ha' := CounterRun.relabel arith code Sum.inr (fun _ => rfl) ha
  have hframe : addressed index = cs index := by
    simp [addressed, atoms, cellAddressAtoms_result _ _ _ _ _ _ _ hit hct hjt, cs₀, hjt]
  have hd := clearCode_run index caller stop addressed ys
  rw [hframe] at hd
  have hd' := CounterRun.relabel suffix arith (arithmeticExit atoms)
    (fun _ => arithmeticCode_embed_fixed _ _ _ _ _) hd
  have hd'' := CounterRun.relabel arith code Sum.inr (fun _ => rfl) hd'
  have h := CounterRun.trans code (CounterRun.trans code hc ha') hd''
  simpa [code, arith, suffix, addressed, atoms, cs₀, cellAddressBindingSteps, cellAddressBindingCounters,
    cellAddressBindingExit, cellAddressAtoms_result _ _ _ _ _ _ _ hit hct hjt, hit, hct, hjt,
    CounterCfg.relabel] using h

end ShiReversibleGenerator
