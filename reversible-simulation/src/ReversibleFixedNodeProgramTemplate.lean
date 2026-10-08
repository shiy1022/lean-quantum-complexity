import ReversibleProgramTemplateSequence
import ReversibleBindingPrinterCleanup
import ReversiblePrinterMonotonicity

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- A fixed list of concrete node emitters with a finite continuation interface. -/
noncomputable def fixedNodeProgramTemplate (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) :
    CounterProgramTemplate R where
  Labels := FixedNodeLabels r ts
  finite := fun L f => by letI := f; infer_instance
  code := fixedNodeCode r ts
  entry := fixedNodeEntry r ts
  exit := fixedNodeExit r ts
  ready := fun cs => cs r.buf=0 ∧ cs r.tmp=0
  steps := fixedNodeSteps r ts
  counters := fixedNodeCounters r ts
  bytes := fixedNodeBytes r ts

theorem fixedNodeProgramTemplate_embeds (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) :
    (fixedNodeProgramTemplate r ts).Embeds := by
  intro L caller stop l
  exact fixedNodeCode_embed r ts caller stop l

theorem fixedNodeProgramTemplate_run (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (hr : r.Valid) (hv : ∀ t ∈ ts,∀ op ∈ t.ops r,op.Valid r.buf r.tmp) :
    (fixedNodeProgramTemplate r ts).Runs := by
  intro L caller stop cs ys hready
  exact fixedNodeCode_run r ts caller stop hr hv cs hready.1 hready.2 ys

theorem fixedNodeProgramTemplate_polynomial (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (bound : Polynomial Nat) : (fixedNodeProgramTemplate r ts).PolynomiallyTimed bound := by
  refine ⟨fixedNodeClock r ts (fun _ => bound),?_⟩
  intro n cs hb hr
  exact fixedNodeSteps_polynomial_bound r ts (fun _ => bound) n cs hb

end ShiReversibleGenerator
