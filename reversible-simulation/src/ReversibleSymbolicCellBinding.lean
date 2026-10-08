import ReversibleCellAddressBinding
import ReversibleIndexExpressionProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev SymbolicCellBindingLabels (p : TickIndexExpr) (input capacity index target : R)
    (offset rank stride : Nat) (L : Type) :=
  IndexExpressionLabels p (CellAddressBindingLabels input capacity index target offset rank stride L)

def symbolicCellBindingExit (p : TickIndexExpr) (input capacity index target : R)
    (offset rank stride : Nat) (l : L) : SymbolicCellBindingLabels p input capacity index target offset rank stride L :=
  indexExpressionExit p (cellAddressBindingExit input capacity index target offset rank stride l)

def symbolicCellBindingCode (p : TickIndexExpr) (caller : L → CounterInstr R L)
    (input capacity position index target tmp : R) (offset rank stride : Nat) (stop : L) :
    SymbolicCellBindingLabels p input capacity index target offset rank stride L →
      CounterInstr R (SymbolicCellBindingLabels p input capacity index target offset rank stride L) :=
  indexExpressionCode p (cellAddressBindingCode caller input capacity index target tmp offset rank stride stop)
    capacity position index tmp (.inl 0)

def symbolicCellBindingSteps (p : TickIndexExpr) (input capacity position index target : R)
    (offset rank stride : Nat) (cs : R → Nat) : Nat :=
  indexExpressionSteps p capacity position index cs +
    cellAddressBindingSteps input capacity index target offset rank stride
      (Function.update cs index (p.eval (cs capacity) (cs position)))

def symbolicCellAddress (p : TickIndexExpr) (input capacity position : R)
    (offset rank stride : Nat) (cs : R → Nat) : Nat :=
  cs input + offset + (rank * stride) * cs capacity + stride * p.eval (cs capacity) (cs position)

/-- A symbolic cell address is actually computed, with the query workspace restored to zero. -/
theorem symbolicCellBindingCode_run (p : TickIndexExpr) (caller : L → CounterInstr R L)
    (input capacity position index target tmp : R) (offset rank stride : Nat) (stop : L)
    (hci : capacity ≠ index) (hpi : position ≠ index) (hbi : input ≠ index)
    (hcx : capacity ≠ tmp) (hpx : position ≠ tmp) (hbx : input ≠ tmp)
    (hit : index ≠ target) (hix : index ≠ tmp) (hbt : input ≠ target)
    (hct : capacity ≠ target) (htx : target ≠ tmp)
    (cs : R → Nat) (hi : cs index = 0) (hx : cs tmp = 0) (ys : List Bool) :
    CounterRun (symbolicCellBindingCode p caller input capacity position index target tmp offset rank stride stop)
      ⟨some (.inl 0), cs, ys⟩ (symbolicCellBindingSteps p input capacity position index target offset rank stride cs)
      ⟨some (symbolicCellBindingExit p input capacity index target offset rank stride stop),
        Function.update cs target (symbolicCellAddress p input capacity position offset rank stride cs), ys⟩ := by
  let inner := cellAddressBindingCode caller input capacity index target tmp offset rank stride stop
  let code := symbolicCellBindingCode p caller input capacity position index target tmp offset rank stride stop
  let cs₁ := Function.update cs index (p.eval (cs capacity) (cs position))
  have h₁ := indexExpressionCode_run p inner capacity position index tmp (.inl 0)
    hci hpi hcx hpx hix cs hx ys
  have h₂ := cellAddressBindingCode_run caller input capacity index target tmp offset rank stride stop
    hbt hct hit hbx hcx hix htx cs₁ (by simp [cs₁, Ne.symm hix, hx]) ys
  have h₂' := CounterRun.relabel inner code (indexExpressionExit p)
    (fun _ => indexExpressionCode_embed _ _ _ _ _ _ _ _) h₂
  have he : cellAddressBindingCounters input capacity index target offset rank stride cs₁ =
      Function.update cs target (symbolicCellAddress p input capacity position offset rank stride cs) := by
    funext r
    by_cases hr : r = index
    · subst r
      simp [cellAddressBindingCounters, symbolicCellAddress, cs₁, hi, hit]
    · by_cases ht : r = target
      · subst r
        simp [cellAddressBindingCounters, symbolicCellAddress, cs₁, hbi, hci, Ne.symm hit]
      · simp [cellAddressBindingCounters, cs₁, hr, ht]
  rw [he] at h₂'
  have h := CounterRun.trans code h₁ h₂'
  simpa [code, inner, cs₁, symbolicCellBindingSteps, symbolicCellBindingExit, CounterCfg.relabel] using h

end ShiReversibleGenerator
