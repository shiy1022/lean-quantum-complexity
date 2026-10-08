import ReversibleLeafCounterTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

noncomputable def guardedLeafCounterTemplate (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (guard : GuardProgramRegisters R)
    (slots : (p : Formula (TickSymbolicCoordinate tm)) → Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (tree : TickGuardFormula tm) : CounterProgramTemplate R :=
  compileGuardedTree guard (fun p => leafPaddedCounterTemplate tm env p (slots p) backward base offset result r) tree

theorem guardedLeafCounterTemplate_run (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (guard : GuardProgramRegisters R) (hg : guard.Valid)
    (slots : (p : Formula (TickSymbolicCoordinate tm)) → Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (tree : TickGuardFormula tm) (hr : r.Valid) (hbase : r.SourceStable base)
    (hresult : r.SourceStable result.source)
    (hv : ∀ p ∈ tree.leaves, ∀ i, (env.withTarget (slots p i)).Valid)
    (hs : ∀ p ∈ tree.leaves, ∀ i, r.SourceStable (slots p i)) :
    (guardedLeafCounterTemplate tm env guard slots backward base offset result r tree).Runs := by
  apply compileGuardedTree_run guard _ tree hg
  · intro p hp; exact leafPaddedCounterTemplate_embeds tm env p (slots p) backward base offset result r
  · intro p hp
    exact leafPaddedCounterTemplate_run tm env p (slots p) (hv p hp) backward base offset result r hr
      hbase (hs p hp) hresult

theorem guardedLeafCounterTemplate_polynomial (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (guard : GuardProgramRegisters R) (hg : guard.Valid)
    (slots : (p : Formula (TickSymbolicCoordinate tm)) → Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (tree : TickGuardFormula tm)
    (hv : ∀ p ∈ tree.leaves, ∀ i, (env.withTarget (slots p i)).Valid) (bound : Polynomial Nat) :
    (guardedLeafCounterTemplate tm env guard slots backward base offset result r tree).PolynomiallyTimed bound := by
  apply compileGuardedTree_polynomial guard _ tree hg bound
  intro p hp
  exact leafPaddedCounterTemplate_polynomial tm env p (slots p) (hv p hp) backward base offset result r bound

theorem guardedLeafCounterTemplate_zero_slots (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (guard : GuardProgramRegisters R)
    (slots : (p : Formula (TickSymbolicCoordinate tm)) → Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (tree : TickGuardFormula tm) (cs : R → Nat) :
    let p := tree.eval (fun g => g.eval (cs guard.capacity) (cs guard.position))
    ∀ i, (guardedLeafCounterTemplate tm env guard slots backward base offset result r tree).counters cs (slots p i) = 0 := by
  intro p i
  unfold guardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  exact leafPaddedCounterTemplate_zero_slots tm env p (slots p) backward base offset result r cs i

/-- Exact bytes of the selected padded compiler from the actual finite whole-tree emitter. -/
theorem guardedLeafCounterTemplate_bytes (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (guard : GuardProgramRegisters R)
    (slots : (p : Formula (TickSymbolicCoordinate tm)) → Fin p.inputList.length → R)
    (backward : Bool) (base : R) (offset bound : Nat) (result : SymbolicWire R) (r : NodePrinterRegisters R)
    (tree : TickGuardFormula tm) (cs : R → Nat)
    (hv : ∀ p ∈ tree.leaves, ∀ i, (env.withTarget (slots p i)).Valid)
    (hi : ∀ p ∈ tree.leaves, Function.Injective (slots p))
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hbase : r.SourceStable base) (hresult : r.SourceStable result.source)
    (hs : ∀ p ∈ tree.leaves, ∀ i, r.SourceStable (slots p i))
    (hz : let p := tree.eval (fun g => g.eval (cs guard.capacity) (cs guard.position))
      let after := coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p (slots p)) cs
      result.eval after = after base + offset + bound) :
    let p := tree.eval (fun g => g.eval (cs guard.capacity) (cs guard.position))
    let after := coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p (slots p)) cs
    let nodes := p.paddedCompile (fun c => tickCoordinateAddress tm env c cs) (after base + offset) bound
    (guardedLeafCounterTemplate tm env guard slots backward base offset result r tree).bytes cs =
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  let p := tree.eval (fun g => g.eval (cs guard.capacity) (cs guard.position))
  have hp : p ∈ tree.leaves := tree.eval_mem_leaves _
  unfold guardedLeafCounterTemplate
  rw [compileGuardedTree_bytes]
  change fixedNodeBytes r (paddedFormulaPrinterTemplates backward p.intern (fun i => ⟨slots p i, 0⟩)
    base offset result) (coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p (slots p)) cs) = _
  rw [paddedFormulaPrinter_bytes backward p.intern (fun i => ⟨slots p i, 0⟩)
    base offset bound result r hpq hpr hqr
    (paddedFormulaPrinter_stable backward p.intern (fun i => ⟨slots p i, 0⟩)
      base offset result r hbase (hs p hp) hresult) _ hz]
  exact leafPaddedFormulaPrinter_payload tm env p (slots p) (hv p hp) (hi p hp) backward cs base offset bound

end ShiReversibleGenerator
