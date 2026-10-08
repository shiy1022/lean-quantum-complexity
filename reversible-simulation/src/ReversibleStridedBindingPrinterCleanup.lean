import ReversibleStridedBindingPrinterBudget
import ReversibleBindingPrinterCleanup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R L : Type} [DecidableEq R]

noncomputable def StridedBindingPrinterCleanupLabels (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (L : Type) : Type :=
  StridedCoordinateBindingSequenceLabels tm env inputStride tasks (FixedNodeLabels r ts (CleanupLabels clear L))

noncomputable def stridedBindingPrinterCleanupCode (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (caller : L → CounterInstr R L) (stop : L) :
    StridedBindingPrinterCleanupLabels tm env inputStride tasks r ts clear L →
      CounterInstr R (StridedBindingPrinterCleanupLabels tm env inputStride tasks r ts clear L) :=
  stridedCoordinateBindingSequenceCode tm env inputStride tasks
    (fixedNodeCode r ts (cleanupCode clear caller stop) (cleanupEntry clear stop))
    (fixedNodeEntry r ts (cleanupEntry clear stop))

noncomputable def stridedBindingPrinterCleanupEntry (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (stop : L) :
    StridedBindingPrinterCleanupLabels tm env inputStride tasks r ts clear L :=
  stridedCoordinateBindingSequenceEntry tm env inputStride tasks (fixedNodeEntry r ts (cleanupEntry clear stop))

noncomputable def stridedBindingPrinterCleanupExit (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (l : L) :
    StridedBindingPrinterCleanupLabels tm env inputStride tasks r ts clear L :=
  stridedCoordinateBindingSequenceExit tm env inputStride tasks (fixedNodeExit r ts (cleanupExit clear l))

noncomputable instance stridedBindingPrinterCleanupFintype (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) [Fintype L] :
    Fintype (StridedBindingPrinterCleanupLabels tm env inputStride tasks r ts clear L) := by
  unfold StridedBindingPrinterCleanupLabels
  infer_instance

/-- Actual binding, finite node printing, and private-register cleanup compose without changing emitted bytes. -/
theorem stridedBindingPrinterCleanupCode_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hops : ∀ t ∈ ts, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (cs : R → Nat) (hq : cs env.query = 0) (hx : cs env.tmp = 0)
    (hb : stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs r.buf = 0)
    (ht : stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs r.tmp = 0) (ys : List Bool) :
    let after := stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs
    let printed := fixedNodeCounters r ts after
    CounterRun (stridedBindingPrinterCleanupCode tm env inputStride tasks r ts clear caller stop)
      ⟨some (stridedBindingPrinterCleanupEntry tm env inputStride tasks r ts clear stop), cs, ys⟩
      (stridedCoordinateBindingSequenceSteps tm env inputStride tasks cs + fixedNodeSteps r ts after + cleanupSteps clear printed)
      ⟨some (stridedBindingPrinterCleanupExit tm env inputStride tasks r ts clear stop), cleanupCounters clear printed,
        fixedNodeBytes r ts after ++ ys⟩ := by
  dsimp only
  let after := stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs
  let inner := cleanupCode clear caller stop
  let printer := fixedNodeCode r ts inner (cleanupEntry clear stop)
  let code := stridedBindingPrinterCleanupCode tm env inputStride tasks r ts clear caller stop
  let embed := fun (l : CleanupLabels clear L) => stridedCoordinateBindingSequenceExit tm env inputStride tasks (fixedNodeExit r ts l)
  have h₁ := stridedCoordinateBindingSequenceCode_run tm env inputStride tasks printer
    (fixedNodeEntry r ts (cleanupEntry clear stop)) hv cs hq hx ys
  have h₂ := fixedNodeCode_run r ts inner (cleanupEntry clear stop) hr hops after hb ht ys
  have h₂' := CounterRun.relabel printer code (stridedCoordinateBindingSequenceExit tm env inputStride tasks)
    (fun l => stridedCoordinateBindingSequenceCode_embed tm env inputStride tasks printer
      (fixedNodeEntry r ts (cleanupEntry clear stop)) l) h₂
  have h₃ := cleanupCode_run clear caller stop (fixedNodeCounters r ts after) (fixedNodeBytes r ts after ++ ys)
  have h₃' := CounterRun.relabel inner code embed (fun l => by
    dsimp only [code, stridedBindingPrinterCleanupCode, embed, printer]
    rw [stridedCoordinateBindingSequenceCode_embed, fixedNodeCode_embed]
    dsimp only [inner]
    cases cleanupCode clear caller stop l <;> rfl) h₃
  have h₁₂ := CounterRun.trans code h₁ h₂'
  have h := CounterRun.trans code h₁₂ h₃'
  simpa only [code, printer, inner, after, embed, stridedBindingPrinterCleanupEntry, stridedBindingPrinterCleanupExit,
    CounterCfg.relabel, Option.map_some] using h


end ShiReversibleGenerator
