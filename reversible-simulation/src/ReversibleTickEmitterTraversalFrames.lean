import ReversibleTickTraversalSupply

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

theorem bindingPrinterTemplate_other_frame (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (r : NodePrinterRegisters R)
    (ts : List (FixedNodeTemplate R)) (clear : List R) (q : R) (cs : R → Nat)
    (hbind : ∀ task ∈ tasks, q ≠ task.2) (hclear : q ∉ clear)
    (hp : q ≠ r.p) (hq : q ≠ r.q) (hr : q ≠ r.r) (hc : q ≠ r.count) :
    (bindingPrinterTemplate tm env tasks r ts clear).counters cs q = cs q := by
  change cleanupCounters clear (fixedNodeCounters r ts (coordinateBindingSequenceCounters tm env tasks cs)) q = _
  rw [cleanupCounters_apply, if_neg hclear, fixedNodeCounters_other r ts q hp hq hr hc,
    coordinateBindingSequence_preserves_other tm env tasks q hbind]

noncomputable def tickTraversalEmitter (tm : Turing.FinTM2) (kind : TickTreeKind tm) (backward : Bool) :
    CounterProgramTemplate (FixedLeafRegister (tickTraversalSupply tm)) :=
  sharedFixedGuardedEmitter (tickTraversalSupply tm) (tickTreeForKind tm kind) backward

theorem tickTraversalEmitter_spare_frame (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (tickTraversalEmitter tm kind backward).counters cs (tickTraversalSpare tm j) = cs (tickTraversalSpare tm j) := by
  unfold tickTraversalEmitter sharedFixedGuardedEmitter guardedLeafCounterTemplate
  rw [compileGuardedTree_counters]
  let p := (tickTreeForKind tm kind).eval (TickIndexGuard.eval (cs (.inl 1)) (cs (.inl 2)))
  have hp : p ∈ (tickTreeForKind tm kind).leaves := DecisionTree.eval_mem_leaves _ _
  have hn := tickTraversalSpare_ne_slot tm kind p hp j
  apply bindingPrinterTemplate_other_frame
  · simp only [leafInputBindingTasks, List.forall_mem_ofFn_iff]
    exact hn
  · simp only [List.mem_ofFn]
    rintro ⟨i, he⟩
    exact hn i he.symm
  all_goals simp [tickTraversalSpare, fixedLeafPrinterRegisters]

theorem tickTraversalEmitter_payload (tm : Turing.FinTM2) (kind : TickTreeKind tm) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (bound : Nat)
    (hz : cs (.inl 13) = cs (.inl 12) + bound) (hi : cs (.inl 2) < cs (.inl 1)) :
    let i : Fin (cs (.inl 1)) := ⟨cs (.inl 2), hi⟩
    let nodes := (boundedTickFormulaForKind tm (cs (.inl 1)) i kind).paddedCompile
      (fun j => cs (.inl 0) + j.val) (cs (.inl 12)) bound
    (tickTraversalEmitter tm kind backward).bytes cs =
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  have h := sharedFixedGuardedEmitter_payload (tickTraversalSupply tm) (tickTreeForKind tm kind)
    (tickTraversalSupply_contains tm kind) backward cs bound hz
  dsimp only at h ⊢
  rw [tickTreeForKind_paddedCompile_relocated tm (cs (.inl 1)) (cs (.inl 0)) (cs (.inl 12)) bound
    ⟨cs (.inl 2), hi⟩ kind] at h
  exact h

theorem tickTraversalEmitter_count (tm : Turing.FinTM2) (kind : TickTreeKind tm) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    let i : Fin (cs (.inl 1)) := ⟨cs (.inl 2), hi⟩
    (tickTraversalEmitter tm kind backward).counters cs (.inl 9) =
      cs (.inl 9) + formulaElementaryLayers (boundedTickFormulaForKind tm (cs (.inl 1)) i kind) + 1 := by
  have h := sharedFixedGuardedEmitter_count (tickTraversalSupply tm) (tickTreeForKind tm kind) backward cs
  have hl := congrArg formulaElementaryLayers
    (tickTreeForKind_formula_agreement tm (cs (.inl 1)) ⟨cs (.inl 2), hi⟩ kind)
  simp only [DecisionTree.evaluate, formulaElementaryLayers_rename] at hl
  dsimp only at h ⊢
  rw [hl] at h
  exact h

end ShiReversibleGenerator
