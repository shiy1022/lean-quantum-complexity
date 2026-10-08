import ReversibleBindingPrinterCertificate
import ReversibleInitializationExactLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R L : Type} [DecidableEq R]

/-- A fixed finite counter program binds a leaf's input addresses and then emits its exact raw circuit payload. -/
theorem leafPaddedFormulaClean_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (backward : Bool) (base : R) (offset bound : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hresult : r.SourceStable result.source) (hbase : r.SourceStable base) (hslots : ∀ i, r.SourceStable (slots i))
    (hbuf : ∀ i, r.buf ≠ slots i) (htmp : ∀ i, r.tmp ≠ slots i)
    (cs : R → Nat) (hq : cs env.query = 0) (hx : cs env.tmp = 0)
    (hb : cs r.buf = 0) (ht : cs r.tmp = 0)
    (hz : let after := coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p slots) cs
      result.eval after = after base + offset + bound) (ys : List Bool) :
    let tasks := leafInputBindingTasks tm p slots
    let after := coordinateBindingSequenceCounters tm env tasks cs
    let ts := paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset result
    let clear := List.ofFn slots
    let code := bindingPrinterCleanupCode tm env tasks r ts clear caller stop
    let nodes := p.paddedCompile (fun coordinate => tickCoordinateAddress tm env coordinate cs) (after base + offset) bound
    CounterRun code ⟨some (bindingPrinterCleanupEntry tm env tasks r ts clear stop), cs, ys⟩
      (coordinateBindingSequenceSteps tm env tasks cs + fixedNodeSteps r ts after +
        cleanupSteps clear (fixedNodeCounters r ts after))
      ⟨some (bindingPrinterCleanupExit tm env tasks r ts clear stop),
        cleanupCounters clear (fixedNodeCounters r ts after),
        ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten ++ ys⟩ := by
  dsimp only
  let tasks := leafInputBindingTasks tm p slots
  let after := coordinateBindingSequenceCounters tm env tasks cs
  let ts := paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset result
  let clear := List.ofFn slots
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
  have h := bindingPrinterCleanupCode_run tm env tasks hv' r ts clear caller stop hr
    (paddedFormulaPrinter_operations_valid backward p.intern (fun i => ⟨slots i, 0⟩)
      base offset result r hr hbase hslots hresult) cs hq hx hbuf' htmp' ys
  dsimp only [ts] at h
  rw [paddedFormulaPrinter_bytes backward p.intern (fun i => ⟨slots i, 0⟩)
    base offset bound result r hpq hpr hqr
    (paddedFormulaPrinter_stable backward p.intern (fun i => ⟨slots i, 0⟩)
      base offset result r hbase hslots hresult) after hz] at h
  rw [leafPaddedFormulaPrinter_payload tm env p slots hv hs backward cs base offset bound] at h
  exact h

/-- All private input slots are zero after the actual leaf program's cleanup. -/
theorem leafPaddedFormulaClean_slots (tm : Turing.FinTM2) (p : Formula (TickSymbolicCoordinate tm))
    (slots : Fin p.inputList.length → R) (cs : R → Nat) (i : Fin p.inputList.length) :
    cleanupCounters (List.ofFn slots) cs (slots i) = 0 := by
  apply bindingPrinterCleanup_zero
  simp only [List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem formulaElementaryLayers_intern {ι : Type} (p : Formula ι) :
    formulaElementaryLayers p.intern = formulaElementaryLayers p := by
  have h := congrArg formulaElementaryLayers p.intern_rename
  simpa only [formulaElementaryLayers_rename] using h

theorem leafPaddedFormulaClean_layers (tm : Turing.FinTM2) (p : Formula (TickSymbolicCoordinate tm))
    (slots : Fin p.inputList.length → R) (backward : Bool) (base : R) (offset : Nat)
    (result : SymbolicWire R) :
    fixedNodeLayerCount (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩)
      base offset result) = formulaElementaryLayers p + 1 := by
  rw [paddedFormulaPrinter_layer_count, formulaElementaryLayers_intern]

end ShiReversibleGenerator
