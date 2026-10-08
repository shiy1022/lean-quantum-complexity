import ReversibleStridedBindingPrinterCleanup
import ReversibleLeafPaddedFormulaClean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R L : Type} [DecidableEq R]

/-- A fixed finite counter program binds a leaf's input addresses and then emits its exact raw circuit payload. -/
theorem stridedLeafPaddedFormulaClean_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (backward : Bool) (base : R) (offset bound : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hresult : r.SourceStable result.source) (hbase : r.SourceStable base) (hslots : ∀ i, r.SourceStable (slots i))
    (hbuf : ∀ i, r.buf ≠ slots i) (htmp : ∀ i, r.tmp ≠ slots i)
    (cs : R → Nat) (hq : cs env.query = 0) (hx : cs env.tmp = 0)
    (hb : cs r.buf = 0) (ht : cs r.tmp = 0)
    (hz : let after := stridedCoordinateBindingSequenceCounters tm env inputStride (leafInputBindingTasks tm p slots) cs
      result.eval after = after base + offset + bound) (ys : List Bool) :
    let tasks := leafInputBindingTasks tm p slots
    let after := stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs
    let ts := paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset result
    let clear := List.ofFn slots
    let code := stridedBindingPrinterCleanupCode tm env inputStride tasks r ts clear caller stop
    let nodes := p.paddedCompile (fun coordinate => stridedTickCoordinateAddress tm env inputStride coordinate cs) (after base + offset) bound
    CounterRun code ⟨some (stridedBindingPrinterCleanupEntry tm env inputStride tasks r ts clear stop), cs, ys⟩
      (stridedCoordinateBindingSequenceSteps tm env inputStride tasks cs + fixedNodeSteps r ts after +
        cleanupSteps clear (fixedNodeCounters r ts after))
      ⟨some (stridedBindingPrinterCleanupExit tm env inputStride tasks r ts clear stop),
        cleanupCounters clear (fixedNodeCounters r ts after),
        ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten ++ ys⟩ := by
  dsimp only
  let tasks := leafInputBindingTasks tm p slots
  let after := stridedCoordinateBindingSequenceCounters tm env inputStride tasks cs
  let ts := paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots i, 0⟩) base offset result
  let clear := List.ofFn slots
  have hv' := leafInputBindingTasks_valid tm env p slots hv
  have hbuf' : after r.buf = 0 := by
    dsimp only [after]
    rw [stridedCoordinateBindingSequence_preserves_other tm env inputStride tasks r.buf]
    · exact hb
    · simpa only [tasks, leafInputBindingTasks, List.forall_mem_ofFn_iff] using hbuf
  have htmp' : after r.tmp = 0 := by
    dsimp only [after]
    rw [stridedCoordinateBindingSequence_preserves_other tm env inputStride tasks r.tmp]
    · exact ht
    · simpa only [tasks, leafInputBindingTasks, List.forall_mem_ofFn_iff] using htmp
  have h := stridedBindingPrinterCleanupCode_run tm env inputStride tasks hv' r ts clear caller stop hr
    (paddedFormulaPrinter_operations_valid backward p.intern (fun i => ⟨slots i, 0⟩)
      base offset result r hr hbase hslots hresult) cs hq hx hbuf' htmp' ys
  dsimp only [ts] at h
  rw [paddedFormulaPrinter_bytes backward p.intern (fun i => ⟨slots i, 0⟩)
    base offset bound result r hpq hpr hqr
    (paddedFormulaPrinter_stable backward p.intern (fun i => ⟨slots i, 0⟩)
      base offset result r hbase hslots hresult) after hz] at h
  rw [stridedLeafPaddedFormulaPrinter_payload tm env inputStride p slots hv hs backward cs base offset bound] at h
  exact h


end ShiReversibleGenerator
