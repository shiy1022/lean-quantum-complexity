import ReversibleIndexExpressionClock
import ReversiblePreservedComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev IndexGuardLabels (g : TickIndexGuard) (L : Type) :=
  IndexExpressionLabels g.left (IndexExpressionLabels g.right (ComparisonLabel L))

def indexGuardExit (g : TickIndexGuard) (l : L) : IndexGuardLabels g L :=
  indexExpressionExit g.left (indexExpressionExit g.right (.inr l))

def indexGuardCode (g : TickIndexGuard) (caller : L → CounterInstr R L)
    (capacity position left right tmp : R) (le gt : L) :
    IndexGuardLabels g L → CounterInstr R (IndexGuardLabels g L) :=
  let cmp := comparisonCode caller left right le gt
  let rhs := indexExpressionCode g.right cmp capacity position right tmp (.inl 0)
  indexExpressionCode g.left rhs capacity position left tmp (.inl 0)

def indexGuardSteps (g : TickIndexGuard) (capacity position left right : R) (cs : R → Nat) : Nat :=
  (indexExpressionSteps g.left capacity position left cs +
    indexExpressionSteps g.right capacity position right
      (Function.update cs left (g.left.eval (cs capacity) (cs position)))) +
    comparisonSteps (g.left.eval (cs capacity) (cs position)) (g.right.eval (cs capacity) (cs position))

/-- Evaluate a fixed guard by actual counter instructions, restoring both guard work counters to zero. -/
theorem indexGuardCode_run (g : TickIndexGuard) (caller : L → CounterInstr R L)
    (capacity position left right tmp : R) (le gt : L)
    (hcl : capacity ≠ left) (hpl : position ≠ left) (hcr : capacity ≠ right) (hpr : position ≠ right)
    (hcx : capacity ≠ tmp) (hpx : position ≠ tmp) (hlx : left ≠ tmp) (hrx : right ≠ tmp)
    (hlr : left ≠ right) (cs : R → Nat) (hl : cs left = 0) (hr : cs right = 0)
    (hx : cs tmp = 0) (ys : List Bool) :
    CounterRun (indexGuardCode g caller capacity position left right tmp le gt)
      ⟨some (.inl 0), cs, ys⟩ (indexGuardSteps g capacity position left right cs)
      ⟨some (indexGuardExit g (if g.eval (cs capacity) (cs position) then le else gt)), cs, ys⟩ := by
  let lhs := g.left.eval (cs capacity) (cs position)
  let rhs := g.right.eval (cs capacity) (cs position)
  let cs₁ := Function.update cs left lhs
  let cmp := comparisonCode caller left right le gt
  let rcode := indexExpressionCode g.right cmp capacity position right tmp (.inl 0)
  let code := indexGuardCode g caller capacity position left right tmp le gt
  have h₁ := indexExpressionCode_run g.left rcode capacity position left tmp (.inl 0)
    hcl hpl hcx hpx hlx cs hx ys
  have hcap : cs₁ capacity = cs capacity := by simp [cs₁, hcl]
  have hpos : cs₁ position = cs position := by simp [cs₁, hpl]
  have htmp : cs₁ tmp = 0 := by simp [cs₁, Ne.symm hlx, hx]
  have h₂ := indexExpressionCode_run g.right cmp capacity position right tmp (.inl 0)
    hcr hpr hcx hpx hrx cs₁ htmp ys
  simp only [hcap, hpos] at h₂
  have h₂' := CounterRun.relabel rcode code (indexExpressionExit g.left)
    (fun _ => indexExpressionCode_embed _ _ _ _ _ _ _ _) h₂
  have hcmp := comparisonCode_run caller left right hlr le gt ⟨none, cs, ys⟩ lhs rhs
  rw [comparisonState_zero cs left right hl hr ys] at hcmp
  change CounterRun cmp
    ⟨some (.inl 0), Function.update (Function.update cs left lhs) right rhs, ys⟩
    (comparisonSteps lhs rhs) ⟨some (.inr (if lhs ≤ rhs then le else gt)), cs, ys⟩ at hcmp
  have hcmp' := CounterRun.relabel cmp rcode (indexExpressionExit g.right)
    (fun _ => indexExpressionCode_embed _ _ _ _ _ _ _ _) hcmp
  have hcmp'' := CounterRun.relabel rcode code (indexExpressionExit g.left)
    (fun _ => indexExpressionCode_embed _ _ _ _ _ _ _ _) hcmp'
  have h := CounterRun.trans code (CounterRun.trans code h₁ h₂') hcmp''
  simpa [code, rcode, cmp, cs₁, lhs, rhs, indexGuardSteps, indexGuardExit, TickIndexGuard.eval,
    CounterCfg.relabel] using h

end ShiReversibleGenerator
