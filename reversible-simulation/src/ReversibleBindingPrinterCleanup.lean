import ReversibleBindingPrinterBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R L : Type} [DecidableEq R]

theorem fixedNodeCode_embed (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (caller : L → CounterInstr R L) (stop l : L) :
    fixedNodeCode r ts caller stop (fixedNodeExit r ts l) = (caller l).relabel (fixedNodeExit r ts) := by
  induction ts with
  | nil =>
    change caller l = (caller l).relabel (fun x => x)
    cases caller l <;> rfl
  | cons t ts ih =>
    change t.code r (fixedNodeCode r ts caller stop) (fixedNodeEntry r ts stop)
      (t.embed r (fixedNodeExit r ts l)) = _
    rw [t.code_embed, ih]
    cases caller l <;> rfl

noncomputable def BindingPrinterCleanupLabels (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (L : Type) : Type :=
  CoordinateBindingSequenceLabels tm env tasks (FixedNodeLabels r ts (CleanupLabels clear L))

noncomputable def bindingPrinterCleanupCode (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (caller : L → CounterInstr R L) (stop : L) :
    BindingPrinterCleanupLabels tm env tasks r ts clear L →
      CounterInstr R (BindingPrinterCleanupLabels tm env tasks r ts clear L) :=
  coordinateBindingSequenceCode tm env tasks
    (fixedNodeCode r ts (cleanupCode clear caller stop) (cleanupEntry clear stop))
    (fixedNodeEntry r ts (cleanupEntry clear stop))

noncomputable def bindingPrinterCleanupEntry (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (stop : L) :
    BindingPrinterCleanupLabels tm env tasks r ts clear L :=
  coordinateBindingSequenceEntry tm env tasks (fixedNodeEntry r ts (cleanupEntry clear stop))

noncomputable def bindingPrinterCleanupExit (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (l : L) :
    BindingPrinterCleanupLabels tm env tasks r ts clear L :=
  coordinateBindingSequenceExit tm env tasks (fixedNodeExit r ts (cleanupExit clear l))

noncomputable instance bindingPrinterCleanupFintype (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) [Fintype L] :
    Fintype (BindingPrinterCleanupLabels tm env tasks r ts clear L) := by
  unfold BindingPrinterCleanupLabels
  infer_instance

/-- Actual binding, finite node printing, and private-register cleanup compose without changing emitted bytes. -/
theorem bindingPrinterCleanupCode_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (hv : ∀ task ∈ tasks, (env.withTarget task.2).Valid)
    (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R)) (clear : List R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hops : ∀ t ∈ ts, ∀ op ∈ t.ops r, op.Valid r.buf r.tmp)
    (cs : R → Nat) (hq : cs env.query = 0) (hx : cs env.tmp = 0)
    (hb : coordinateBindingSequenceCounters tm env tasks cs r.buf = 0)
    (ht : coordinateBindingSequenceCounters tm env tasks cs r.tmp = 0) (ys : List Bool) :
    let after := coordinateBindingSequenceCounters tm env tasks cs
    let printed := fixedNodeCounters r ts after
    CounterRun (bindingPrinterCleanupCode tm env tasks r ts clear caller stop)
      ⟨some (bindingPrinterCleanupEntry tm env tasks r ts clear stop), cs, ys⟩
      (coordinateBindingSequenceSteps tm env tasks cs + fixedNodeSteps r ts after + cleanupSteps clear printed)
      ⟨some (bindingPrinterCleanupExit tm env tasks r ts clear stop), cleanupCounters clear printed,
        fixedNodeBytes r ts after ++ ys⟩ := by
  dsimp only
  let after := coordinateBindingSequenceCounters tm env tasks cs
  let inner := cleanupCode clear caller stop
  let printer := fixedNodeCode r ts inner (cleanupEntry clear stop)
  let code := bindingPrinterCleanupCode tm env tasks r ts clear caller stop
  let embed := fun (l : CleanupLabels clear L) => coordinateBindingSequenceExit tm env tasks (fixedNodeExit r ts l)
  have h₁ := coordinateBindingSequenceCode_run tm env tasks printer
    (fixedNodeEntry r ts (cleanupEntry clear stop)) hv cs hq hx ys
  have h₂ := fixedNodeCode_run r ts inner (cleanupEntry clear stop) hr hops after hb ht ys
  have h₂' := CounterRun.relabel printer code (coordinateBindingSequenceExit tm env tasks)
    (fun l => coordinateBindingSequenceCode_embed tm env tasks printer
      (fixedNodeEntry r ts (cleanupEntry clear stop)) l) h₂
  have h₃ := cleanupCode_run clear caller stop (fixedNodeCounters r ts after) (fixedNodeBytes r ts after ++ ys)
  have h₃' := CounterRun.relabel inner code embed (fun l => by
    dsimp only [code, bindingPrinterCleanupCode, embed, printer]
    rw [coordinateBindingSequenceCode_embed, fixedNodeCode_embed]
    dsimp only [inner]
    cases cleanupCode clear caller stop l <;> rfl) h₃
  have h₁₂ := CounterRun.trans code h₁ h₂'
  have h := CounterRun.trans code h₁₂ h₃'
  simpa only [code, printer, inner, after, embed, bindingPrinterCleanupEntry, bindingPrinterCleanupExit,
    CounterCfg.relabel, Option.map_some] using h

theorem bindingPrinterCleanup_zero (clear : List R) (cs : R → Nat) (q : R) (hq : q ∈ clear) :
    cleanupCounters clear cs q = 0 := by
  simp [cleanupCounters_apply, hq]

end ShiReversibleGenerator
