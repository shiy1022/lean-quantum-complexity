import ReversiblePrinterMonotonicity
import ReversiblePreservedComparison

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R L : Type} [DecidableEq R]

abbrev ChoicePrinterLabels (r : NodePrinterRegisters R) (yes no : List (FixedNodeTemplate R)) (L : Type) :=
  FixedNodeLabels r yes (FixedNodeLabels r no L)

def choicePrinterCode (r : NodePrinterRegisters R) (yes no : List (FixedNodeTemplate R))
    (caller : L → CounterInstr R L) (stop : L) :
    ChoicePrinterLabels r yes no L → CounterInstr R (ChoicePrinterLabels r yes no L) :=
  fixedNodeCode r yes (fixedNodeCode r no caller stop) (fixedNodeExit r no stop)

def choicePrinterEntry (r : NodePrinterRegisters R) (yes no : List (FixedNodeTemplate R))
    (stop : L) (b : Bool) : ChoicePrinterLabels r yes no L :=
  if b then fixedNodeEntry r yes (fixedNodeExit r no stop)
    else fixedNodeExit r yes (fixedNodeEntry r no stop)

def choicePrinterExit (r : NodePrinterRegisters R) (yes no : List (FixedNodeTemplate R))
    (stop : L) : ChoicePrinterLabels r yes no L :=
  fixedNodeExit r yes (fixedNodeExit r no stop)

theorem fixedNodeCode_exit (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (caller : L → CounterInstr R L) (stop l : L) :
    fixedNodeCode r ts caller stop (fixedNodeExit r ts l) =
      (caller l).relabel (fixedNodeExit r ts) := by
  induction ts with
  | nil =>
      simp only [fixedNodeCode, fixedNodeExit]
      cases caller l <;> rfl
  | cons t ts ih =>
      rw [fixedNodeCode, fixedNodeExit, t.code_embed, ih]
      cases caller l <;> rfl

theorem choicePrinter_run (r : NodePrinterRegisters R) (yes no : List (FixedNodeTemplate R))
    (caller : L → CounterInstr R L) (stop : L) (b : Bool) (hr : r.Valid)
    (hy : ∀ t ∈ yes, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (hn : ∀ t ∈ no, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (cs : R → Nat) (hb : cs r.buf = 0) (ht : cs r.tmp = 0) (ys : List Bool) :
    CounterRun (choicePrinterCode r yes no caller stop)
      ⟨some (choicePrinterEntry r yes no stop b), cs, ys⟩
      (fixedNodeSteps r (if b then yes else no) cs)
      ⟨some (choicePrinterExit r yes no stop), fixedNodeCounters r (if b then yes else no) cs,
        fixedNodeBytes r (if b then yes else no) cs ++ ys⟩ := by
  cases b with
  | true => exact fixedNodeCode_run r yes (fixedNodeCode r no caller stop) (fixedNodeExit r no stop) hr hy cs hb ht ys
  | false =>
      have h := fixedNodeCode_run r no caller stop hr hn cs hb ht ys
      have h' := CounterRun.relabel (fixedNodeCode r no caller stop)
        (choicePrinterCode r yes no caller stop) (fixedNodeExit r yes)
        (fixedNodeCode_exit r yes _ (fixedNodeExit r no stop)) h
      exact h'

abbrev ConditionalPrinterLabels (r : NodePrinterRegisters R)
    (yes no : List (FixedNodeTemplate R)) (a b ca cb : R) (L : Type) :=
  GeneratorOperationLabels (comparisonCopies a b ca cb) (ComparisonLabel (ChoicePrinterLabels r yes no L))

def conditionalPrinterCode (r : NodePrinterRegisters R) (yes no : List (FixedNodeTemplate R))
    (a b ca cb : R) (caller : L → CounterInstr R L) (stop : L) :
    ConditionalPrinterLabels r yes no a b ca cb L →
      CounterInstr R (ConditionalPrinterLabels r yes no a b ca cb L) :=
  operationCode (comparisonCopies a b ca cb)
    (comparisonCode (choicePrinterCode r yes no caller stop) ca cb
      (choicePrinterEntry r yes no stop true) (choicePrinterEntry r yes no stop false))
    r.buf r.tmp (.inl 0)

/-- The dynamic guard is executed by actual counter instructions before printing either fixed schema. -/
theorem conditionalPrinter_run (r : NodePrinterRegisters R) (yes no : List (FixedNodeTemplate R))
    (a b ca cb : R) (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hy : ∀ t ∈ yes, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (hn : ∀ t ∈ no, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (hv : ∀ op ∈ comparisonCopies a b ca cb, op.Valid r.buf r.tmp)
    (hbc : b ≠ ca) (hcacb : ca ≠ cb)
    (cs : R → Nat) (hca : cs ca = 0) (hcb : cs cb = 0)
    (hb : cs r.buf = 0) (ht : cs r.tmp = 0) (ys : List Bool) :
    let selected := if cs a ≤ cs b then yes else no
    let embed := fun l => operationExit (comparisonCopies a b ca cb) (Sum.inr l)
    CounterRun (conditionalPrinterCode r yes no a b ca cb caller stop)
      ⟨some (operationEntry (comparisonCopies a b ca cb) (.inl 0)), cs, ys⟩
      (operationSteps (comparisonCopies a b ca cb) cs + comparisonSteps (cs a) (cs b) +
        fixedNodeSteps r selected cs)
      ⟨some (embed (choicePrinterExit r yes no stop)), fixedNodeCounters r selected cs,
        fixedNodeBytes r selected cs ++ ys⟩ := by
  let choice := choicePrinterCode r yes no caller stop
  let code := conditionalPrinterCode r yes no a b ca cb caller stop
  let embed := fun (l : ChoicePrinterLabels r yes no L) =>
    operationExit (comparisonCopies a b ca cb) (Sum.inr l : ComparisonLabel (ChoicePrinterLabels r yes no L))
  have hc := preservedComparison_run choice a b ca cb r.buf r.tmp
    (choicePrinterEntry r yes no stop true) (choicePrinterEntry r yes no stop false)
    hv hr.2.2.2.2.2.2.2.2.2 hbc hcacb cs hca hcb hb ht ys
  have hp := choicePrinter_run r yes no caller stop (decide (cs a ≤ cs b)) hr hy hn cs hb ht ys
  have hf : ∀ l, code (embed l) = (choice l).relabel embed := by
    intro l
    simp only [code, conditionalPrinterCode, embed, operationCode_embed, comparisonCode]
    exact CounterInstr.relabel_comp Sum.inr (operationExit (comparisonCopies a b ca cb)) (choice l)
  have hp' := CounterRun.relabel choice code embed hf hp
  by_cases h : cs a ≤ cs b
  · simp only [h, if_true, decide_true] at hc hp' ⊢
    exact CounterRun.trans code hc hp'
  · simp only [h, if_false, decide_false] at hc hp' ⊢
    exact CounterRun.trans code hc hp'

end ShiReversibleGenerator
