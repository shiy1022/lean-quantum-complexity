import ReversibleStridedBindingPrinterCertificate
import ReversibleBindingPrinterTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- The previously checked concrete emitter, packaged for structural guard-tree compilation. -/
noncomputable def stridedBindingPrinterTemplate (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) : CounterProgramTemplate R where
  Labels := StridedBindingPrinterCleanupLabels tm env inputStride tasks r ts clear
  finite := fun L f => by letI := f; infer_instance
  code := stridedBindingPrinterCleanupCode tm env inputStride tasks r ts clear
  entry := stridedBindingPrinterCleanupEntry tm env inputStride tasks r ts clear
  exit := stridedBindingPrinterCleanupExit tm env inputStride tasks r ts clear
  ready := fun cs => cs env.query = 0 ∧ cs env.tmp = 0 ∧
    stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs r.buf = 0 ∧
    stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs r.tmp = 0
  steps := fun cs => let after := stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs
    stridedCoordinateBindingSequenceSteps tm env inputStride tasks cs + fixedNodeSteps r ts after +
      cleanupSteps clear (fixedNodeCounters r ts after)
  counters := fun cs => cleanupCounters clear (fixedNodeCounters r ts
    (stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs))
  bytes := fun cs => fixedNodeBytes r ts (stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs)

theorem stridedBindingPrinterTemplate_embeds (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) :
    (stridedBindingPrinterTemplate tm env inputStride tasks r ts clear).Embeds := by
  intro L caller stop l
  change stridedBindingPrinterCleanupCode tm env inputStride tasks r ts clear caller stop
    (stridedBindingPrinterCleanupExit tm env inputStride tasks r ts clear l) = _
  unfold stridedBindingPrinterCleanupCode stridedBindingPrinterCleanupExit
  rw [stridedCoordinateBindingSequenceCode_embed, fixedNodeCode_embed, cleanupCode_embed]
  cases caller l <;> rfl

theorem stridedBindingPrinterTemplate_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R) (hr : r.Valid)
    (hops : ∀ t ∈ ts, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp) :
    (stridedBindingPrinterTemplate tm env inputStride tasks r ts clear).Runs := by
  intro L caller stop cs ys hready
  rcases hready with ⟨hq, hx, hb, ht⟩
  exact stridedBindingPrinterCleanupCode_run tm env inputStride tasks hv r ts clear caller stop hr hops cs hq hx hb ht ys

theorem stridedBindingPrinterTemplate_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R) (bound : Polynomial Nat) :
    (stridedBindingPrinterTemplate tm env inputStride tasks r ts clear).PolynomiallyTimed bound := by
  obtain ⟨clock, hc⟩ := stridedCoordinateBindingPrinterCleanup_polynomial tm env inputStride tasks hv r ts clear bound
  exact ⟨clock, fun n cs hb _ => hc n cs hb⟩

end ShiReversibleGenerator
