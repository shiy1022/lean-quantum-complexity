import ReversibleIndexExpressionRecipe
import ReversibleAddressBinding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev IndexExpressionLabels (p : TickIndexExpr) (L : Type) :=
  AddressBindingLabels p.seed.offset p.seed.coefficient 0 (IndexUpdateLabels p.updates L)

def indexExpressionExit (p : TickIndexExpr) (l : L) : IndexExpressionLabels p L :=
  .inr (.inr (.inr (.inr (indexUpdateExit p.updates l))))

def indexExpressionCode (p : TickIndexExpr) (caller : L → CounterInstr R L)
    (capacity position target tmp : R) (stop : L) :
    IndexExpressionLabels p L → CounterInstr R (IndexExpressionLabels p L) :=
  addressBindingCode (indexUpdateCode p.updates caller target stop)
    (p.seed.source capacity position) target tmp p.seed.offset p.seed.coefficient 0
    (indexUpdateEntry p.updates stop)

def indexExpressionSteps (p : TickIndexExpr) (capacity position target : R) (cs : R → Nat) : Nat :=
  ((2 * cs target + 1) + (p.seed.coefficient * (7 * cs (p.seed.source capacity position) + 2) + p.seed.offset)) +
    indexUpdateSteps p.updates

theorem addressBindingCode_embed (caller : L → CounterInstr R L) (source target tmp : R)
    (positive coefficient negative : Nat) (stop l : L) :
    addressBindingCode caller source target tmp positive coefficient negative stop (.inr (.inr (.inr (.inr l)))) =
      (caller l).relabel (fun x => .inr (.inr (.inr (.inr x)))) := by
  change ((((caller l).relabel Sum.inr).relabel Sum.inr).relabel Sum.inr).relabel Sum.inr = _
  cases caller l <;> rfl

/-- Execute a fixed index expression with exact clock, preserving input counters and the output tail. -/
theorem indexExpressionCode_run (p : TickIndexExpr) (caller : L → CounterInstr R L)
    (capacity position target tmp : R) (stop : L)
    (hct : capacity ≠ target) (hpt : position ≠ target)
    (hcx : capacity ≠ tmp) (hpx : position ≠ tmp) (htx : target ≠ tmp)
    (cs : R → Nat) (hx : cs tmp = 0) (ys : List Bool) :
    CounterRun (indexExpressionCode p caller capacity position target tmp stop)
      ⟨some (.inl 0), cs, ys⟩ (indexExpressionSteps p capacity position target cs)
      ⟨some (indexExpressionExit p stop),
        Function.update cs target (p.eval (cs capacity) (cs position)), ys⟩ := by
  let source := p.seed.source capacity position
  have hst : source ≠ target := by
    cases h : p.seed with
    | position => simpa [source, h, TickIndexSeed.source] using hpt
    | capacity => simpa [source, h, TickIndexSeed.source] using hct
    | literal n => simpa [source, h, TickIndexSeed.source] using hpt
  have hsx : source ≠ tmp := by
    cases h : p.seed with
    | position => simpa [source, h, TickIndexSeed.source] using hpx
    | capacity => simpa [source, h, TickIndexSeed.source] using hcx
    | literal n => simpa [source, h, TickIndexSeed.source] using hpx
  let inner := indexUpdateCode p.updates caller target stop
  let code := indexExpressionCode p caller capacity position target tmp stop
  have h₁ := addressBindingCode_run inner source target tmp p.seed.offset p.seed.coefficient 0
    (indexUpdateEntry p.updates stop) hst hsx htx cs hx ys
  have hseed := TickIndexSeed.affine_eval p.seed capacity position cs
  simp only [source, Nat.add_zero, Nat.sub_zero, hseed] at h₁
  have h₂ := indexUpdateCode_run p.updates caller target stop
    (Function.update cs target (p.seed.eval (cs capacity) (cs position))) ys
  have h₃ := CounterRun.relabel inner code (fun x => .inr (.inr (.inr (.inr x))))
    (fun _ => addressBindingCode_embed _ _ _ _ _ _ _ _ _) h₂
  have h := CounterRun.trans code h₁ h₃
  simpa [code, inner, source, indexExpressionSteps, indexExpressionExit, TickIndexExpr.recipe_eval, CounterCfg.relabel] using h

theorem indexExpressionCode_embed (p : TickIndexExpr) (caller : L → CounterInstr R L)
    (capacity position target tmp : R) (stop l : L) :
    indexExpressionCode p caller capacity position target tmp stop (indexExpressionExit p l) =
      (caller l).relabel (indexExpressionExit p) := by
  rw [indexExpressionCode, indexExpressionExit, addressBindingCode_embed, indexUpdateCode_embed]
  cases caller l <;> rfl

end ShiReversibleGenerator
