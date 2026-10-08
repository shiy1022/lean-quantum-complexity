import ReversibleInitializationSchema
import ReversibleConditionalPrinterBounds

set_option autoImplicit false
namespace ShiReversibleFormula

theorem Formula.rename_paddedCompile {ι κ : Type} (p : Formula ι) (f : ι → κ)
    (inputs : κ → Nat) (base bound : Nat) :
    (p.rename f).paddedCompile inputs base bound =
      p.paddedCompile (fun i => inputs (f i)) base bound := by
  simp [Formula.paddedCompile, Formula.rename_rawCompile, Formula.rename_size, Formula.result]

end ShiReversibleFormula

namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM ShiReversibleCoding
variable {R L : Type} [DecidableEq R]
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

noncomputable def initializationYesTemplates (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (wire base result : R) :=
  paddedFormulaPrinterTemplates backward (initializationInputCellSchema tm e a)
    (fun _ => (⟨wire, 0⟩ : SymbolicWire R)) base 0 ⟨result, 0⟩

noncomputable def initializationNoTemplates (tm : Turing.FinTM2) (a : Option (MachineSymbol tm))
    (backward : Bool) (wire base result : R) :=
  paddedFormulaPrinterTemplates backward (.constant (oneHot none a) : Formula Unit)
    (fun _ => (⟨wire, 0⟩ : SymbolicWire R)) base 0 ⟨result, 0⟩

noncomputable def initializationCellPayload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (a : Option (MachineSymbol tm))
    (backward : Bool) (base : Nat) : List Bool :=
  let nodes := ((initialFormulas tm e capacity n).cells tm.k₀ i a).paddedCompile
    (fun j => j.val) base 17
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

/-- Runtime i<n chooses two fixed schemas, and both serialize the existing padded initializer. -/
theorem initializationCellPrinter_bytes (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (a : Option (MachineSymbol tm)) (backward : Bool)
    (wire base result next length : R) (r : NodePrinterRegisters R)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hw : r.SourceStable wire) (hbase : r.SourceStable base) (hresult : r.SourceStable result)
    (cs : R → Nat) (hi : cs wire = i.val) (hn : cs length = n) (hs : cs next = i.val + 1)
    (hz : cs result = cs base + 17) :
    fixedNodeBytes r (if cs next ≤ cs length then
      initializationYesTemplates tm e a backward wire base result
      else initializationNoTemplates tm a backward wire base result) cs =
      initializationCellPayload tm e capacity n i a backward (cs base) := by
  have hy := paddedFormulaPrinter_bytes backward (initializationInputCellSchema tm e a)
    (fun _ => (⟨wire, 0⟩ : SymbolicWire R)) base 0 17 ⟨result, 0⟩ r hpq hpr hqr
    (paddedFormulaPrinter_stable backward _ _ base 0 ⟨result, 0⟩ r hbase (fun _ => hw) hresult)
    cs (by simpa [SymbolicWire.eval] using hz)
  have he := paddedFormulaPrinter_bytes backward (.constant (oneHot none a) : Formula Unit)
    (fun _ => (⟨wire, 0⟩ : SymbolicWire R)) base 0 17 ⟨result, 0⟩ r hpq hpr hqr
    (paddedFormulaPrinter_stable backward _ _ base 0 ⟨result, 0⟩ r hbase (fun _ => hw) hresult)
    cs (by simpa [SymbolicWire.eval] using hz)
  by_cases hit : i.val < n
  · have hg : cs next ≤ cs length := by omega
    simp only [hg, if_true, initializationYesTemplates]
    rw [hy]
    unfold initializationCellPayload
    rw [initialFormulas_input_cell_schema tm e capacity n i hit a, Formula.rename_paddedCompile]
    simp [paddedFormulaPrinterPayload, SymbolicWire.eval, hi]
  · have hg : ¬ cs next ≤ cs length := by omega
    simp only [hg, if_false, initializationNoTemplates]
    rw [he]
    unfold initializationCellPayload
    rw [initialFormulas_padding_cell_schema tm e capacity n tm.k₀ i a (Or.inr (by omega))]
    cases backward <;> simp [paddedFormulaPrinterPayload, Formula.paddedCompile,
      Formula.rawCompile, Formula.size, Formula.result, rawAssignmentPayload,
      assignmentPayload, assignmentAtoms, emissionBytes]

/-- Actual comparison and printing instructions, with the precise initializer payload. -/
theorem initializationCellPrinter_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (a : Option (MachineSymbol tm)) (backward : Bool)
    (wire base result next length ca cb : R) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hw : r.SourceStable wire) (hbase : r.SourceStable base) (hresult : r.SourceStable result)
    (hv : ∀ op ∈ comparisonCopies next length ca cb, op.Valid r.buf r.tmp)
    (hlca : length ≠ ca) (hcacb : ca ≠ cb)
    (cs : R → Nat) (hi : cs wire = i.val) (hn : cs length = n) (hs : cs next = i.val + 1)
    (hz : cs result = cs base + 17) (hca : cs ca = 0) (hcb : cs cb = 0)
    (hb : cs r.buf = 0) (ht : cs r.tmp = 0) (ys : List Bool) :
    let yes := initializationYesTemplates tm e a backward wire base result
    let no := initializationNoTemplates tm a backward wire base result
    let selected := if cs next ≤ cs length then yes else no
    CounterRun (conditionalPrinterCode r yes no next length ca cb caller stop)
      ⟨some (operationEntry (comparisonCopies next length ca cb) (.inl 0)), cs, ys⟩
      (operationSteps (comparisonCopies next length ca cb) cs + comparisonSteps (cs next) (cs length) +
        fixedNodeSteps r selected cs)
      ⟨some (operationExit (comparisonCopies next length ca cb) (.inr (choicePrinterExit r yes no stop))),
        fixedNodeCounters r selected cs,
        initializationCellPayload tm e capacity n i a backward (cs base) ++ ys⟩ := by
  have h := conditionalPrinter_run r (initializationYesTemplates tm e a backward wire base result)
    (initializationNoTemplates tm a backward wire base result) next length ca cb caller stop hr
    (paddedFormulaPrinter_operations_valid backward _ _ base 0 ⟨result, 0⟩ r hr hbase (fun _ => hw) hresult)
    (paddedFormulaPrinter_operations_valid backward _ _ base 0 ⟨result, 0⟩ r hr hbase (fun _ => hw) hresult)
    hv hlca hcacb cs hca hcb hb ht ys
  dsimp only at h
  rw [initializationCellPrinter_bytes tm e capacity n i a backward wire base result next length r
    hpq hpr hqr hw hbase hresult cs hi hn hs hz] at h
  exact h

end ShiReversibleGenerator
