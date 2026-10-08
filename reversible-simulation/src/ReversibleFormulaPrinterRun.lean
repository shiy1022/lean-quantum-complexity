import ReversibleFormulaSources

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R L : Type} [DecidableEq R]

def formulaPrinterPayload {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (cs : R → Nat) : List Bool :=
  let nodes := p.rawCompile (fun i => (inputs i).eval cs) (cs base + offset)
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

/-- Actual finite formula printer, with its source and instruction validity derived. -/
theorem formulaPrinter_run {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hbase : r.SourceStable base) (hi : ∀ i, r.SourceStable (inputs i).source)
    (cs : R → Nat) (hb : cs r.buf = 0) (ht : cs r.tmp = 0) (ys : List Bool) :
    let ts := formulaPrinterTemplates backward p inputs base offset
    CounterRun (fixedNodeCode r ts caller stop) ⟨some (fixedNodeEntry r ts stop), cs, ys⟩
      (fixedNodeSteps r ts cs) ⟨some (fixedNodeExit r ts stop), fixedNodeCounters r ts cs,
        formulaPrinterPayload backward p inputs base offset cs ++ ys⟩ := by
  have h := fixedNodeCode_run r (formulaPrinterTemplates backward p inputs base offset) caller stop hr
    (formulaPrinter_operations_valid backward p inputs base offset r hr hbase hi) cs hb ht ys
  rw [formulaPrinter_bytes backward p inputs base offset r hpq hpr hqr
    (formulaPrinter_stable backward p inputs base offset r hbase hi) cs] at h
  cases backward <;> simpa [formulaPrinterPayload] using h

theorem fixedNodeCounters_other (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (s : R) (hp : s ≠ r.p) (hq : s ≠ r.q) (hr : s ≠ r.r) (hc : s ≠ r.count)
    (cs : R → Nat) : fixedNodeCounters r ts cs s = cs s := by
  induction ts generalizing cs with
  | nil => rfl
  | cons t ts ih =>
      rw [fixedNodeCounters, ih]
      exact t.counters_other r s hp hq hr hc cs

theorem formulaPrinter_preserves_sources {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (s : R) (hs : r.SourceStable s) (cs : R → Nat) :
    fixedNodeCounters r (formulaPrinterTemplates backward p inputs base offset) cs s = cs s :=
  fixedNodeCounters_other r _ s hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 cs

theorem formulaPrinter_clock {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (sizes : R → Polynomial Nat) : ∃ clock : Polynomial Nat, ∀ n,
    fixedNodeSteps r (formulaPrinterTemplates backward p inputs base offset)
      (fun s => (sizes s).eval n) = clock.eval n := by
  exact ⟨fixedNodeClock r (formulaPrinterTemplates backward p inputs base offset) sizes,
    fun n => (fixedNodeClock_eval r _ sizes n).symm⟩

end ShiReversibleGenerator
