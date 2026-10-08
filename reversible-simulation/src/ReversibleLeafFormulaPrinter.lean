import ReversibleBindingSequenceContinuation
import ReversibleFormulaPrinterRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R L : Type} [DecidableEq R]

theorem leafFormulaPrinter_payload (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (backward : Bool) (cs : R → Nat) (base : R) (offset : Nat) :
    let after := coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p slots) cs
    formulaPrinterPayload backward p.intern (fun i => ⟨slots i, 0⟩) base offset after =
      let nodes := p.rawCompile (fun coordinate => tickCoordinateAddress tm env coordinate cs) (after base + offset)
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  dsimp only
  have h := leafInputBindings_compile_eval tm env p slots hv hs cs base offset
  dsimp only at h
  rw [symbolicFormulaCompile_eval] at h
  unfold formulaPrinterPayload
  rw [h]

/-- A fixed finite counter program binds a leaf's input addresses and then emits its exact raw circuit payload. -/
theorem leafFormulaPrinter_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (backward : Bool) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hbase : r.SourceStable base) (hslots : ∀ i, r.SourceStable (slots i))
    (hbuf : ∀ i, r.buf ≠ slots i) (htmp : ∀ i, r.tmp ≠ slots i)
    (cs : R → Nat) (hq : cs env.query = 0) (hx : cs env.tmp = 0)
    (hb : cs r.buf = 0) (ht : cs r.tmp = 0) (ys : List Bool) :
    let tasks := leafInputBindingTasks tm p slots
    let after := coordinateBindingSequenceCounters tm env tasks cs
    let ts := formulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset
    let printer := fixedNodeCode r ts caller stop
    let printerStart := fixedNodeEntry r ts stop
    let code := coordinateBindingSequenceCode tm env tasks printer printerStart
    let nodes := p.rawCompile (fun coordinate => tickCoordinateAddress tm env coordinate cs) (after base + offset)
    CounterRun code ⟨some (coordinateBindingSequenceEntry tm env tasks printerStart), cs, ys⟩
      (coordinateBindingSequenceSteps tm env tasks cs + fixedNodeSteps r ts after)
      ⟨some (coordinateBindingSequenceExit tm env tasks (fixedNodeExit r ts stop)),
        fixedNodeCounters r ts after,
        ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten ++ ys⟩ := by
  dsimp only
  let tasks := leafInputBindingTasks tm p slots
  let after := coordinateBindingSequenceCounters tm env tasks cs
  let ts := formulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset
  let printer := fixedNodeCode r ts caller stop
  let start := fixedNodeEntry r ts stop
  let code := coordinateBindingSequenceCode tm env tasks printer start
  have hv' := leafInputBindingTasks_valid tm env p slots hv
  have hbuf' : after r.buf = 0 := by
    dsimp only [after]
    rw [coordinateBindingSequence_preserves_other tm env tasks r.buf]
    · exact hb
    · simpa only [tasks, leafInputBindingTasks, List.forall_mem_ofFn_iff] using hbuf
  have htmp' : after r.tmp = 0 := by
    dsimp only [after]
    rw [coordinateBindingSequence_preserves_other tm env tasks r.tmp]
    · exact ht
    · simpa only [tasks, leafInputBindingTasks, List.forall_mem_ofFn_iff] using htmp
  have h₁ := coordinateBindingSequenceCode_run tm env tasks printer start hv' cs hq hx ys
  have h₂ := formulaPrinter_run backward p.intern (fun i => ⟨slots i, 0⟩) base offset r caller stop hr
    hpq hpr hqr hbase hslots after hbuf' htmp' ys
  dsimp only at h₂
  rw [leafFormulaPrinter_payload tm env p slots hv hs backward cs base offset] at h₂
  have h₃ := CounterRun.relabel printer code (coordinateBindingSequenceExit tm env tasks)
    (fun l => coordinateBindingSequenceCode_embed tm env tasks printer start l) h₂
  have h := CounterRun.trans code h₁ h₃
  simpa only [code, printer, start, tasks, ts, after, CounterCfg.relabel, Option.map_some] using h

end ShiReversibleGenerator
