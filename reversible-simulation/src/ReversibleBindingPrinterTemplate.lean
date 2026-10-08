import ReversibleGuardedTreeCompiler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- The previously checked concrete emitter, packaged for structural guard-tree compilation. -/
noncomputable def bindingPrinterTemplate (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) : CounterProgramTemplate R where
  Labels := BindingPrinterCleanupLabels tm env tasks r ts clear
  finite := fun L f => by letI := f; infer_instance
  code := bindingPrinterCleanupCode tm env tasks r ts clear
  entry := bindingPrinterCleanupEntry tm env tasks r ts clear
  exit := bindingPrinterCleanupExit tm env tasks r ts clear
  ready := fun cs => cs env.query = 0 ∧ cs env.tmp = 0 ∧
    coordinateBindingSequenceCounters tm env tasks cs r.buf = 0 ∧
    coordinateBindingSequenceCounters tm env tasks cs r.tmp = 0
  steps := fun cs => let after := coordinateBindingSequenceCounters tm env tasks cs
    coordinateBindingSequenceSteps tm env tasks cs + fixedNodeSteps r ts after +
      cleanupSteps clear (fixedNodeCounters r ts after)
  counters := fun cs => cleanupCounters clear (fixedNodeCounters r ts
    (coordinateBindingSequenceCounters tm env tasks cs))
  bytes := fun cs => fixedNodeBytes r ts (coordinateBindingSequenceCounters tm env tasks cs)

theorem bindingPrinterTemplate_embeds (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) :
    (bindingPrinterTemplate tm env tasks r ts clear).Embeds := by
  intro L caller stop l
  change bindingPrinterCleanupCode tm env tasks r ts clear caller stop
    (bindingPrinterCleanupExit tm env tasks r ts clear l) = _
  unfold bindingPrinterCleanupCode bindingPrinterCleanupExit
  rw [coordinateBindingSequenceCode_embed, fixedNodeCode_embed, cleanupCode_embed]
  cases caller l <;> rfl

theorem bindingPrinterTemplate_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R) (hr : r.Valid)
    (hops : ∀ t ∈ ts, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp) :
    (bindingPrinterTemplate tm env tasks r ts clear).Runs := by
  intro L caller stop cs ys hready
  rcases hready with ⟨hq, hx, hb, ht⟩
  exact bindingPrinterCleanupCode_run tm env tasks hv r ts clear caller stop hr hops cs hq hx hb ht ys

theorem bindingPrinterTemplate_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R) (bound : Polynomial Nat) :
    (bindingPrinterTemplate tm env tasks r ts clear).PolynomiallyTimed bound := by
  obtain ⟨clock, hc⟩ := coordinateBindingPrinterCleanup_polynomial tm env tasks hv r ts clear bound
  exact ⟨clock, fun n cs hb _ => hc n cs hb⟩

end ShiReversibleGenerator
