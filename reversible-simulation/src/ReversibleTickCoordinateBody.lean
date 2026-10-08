import ReversibleProgramTemplateSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickTraversalEmitter_embeds (tm : Turing.FinTM2) (kind : TickTreeKind tm) (backward : Bool) :
    (tickTraversalEmitter tm kind backward).Embeds := by
  unfold tickTraversalEmitter sharedFixedGuardedEmitter guardedLeafCounterTemplate
  apply compileGuardedTree_embeds
  intro p hp
  exact leafPaddedCounterTemplate_embeds tm _ p _ backward _ _ _ _

noncomputable def tickCoordinateBody (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (bound : Nat) (backward : Bool) : CounterProgramTemplate (FixedLeafRegister (tickTraversalSupply tm)) :=
  sequenceProgramTemplate (tickOutputPreparationTemplate tm kind bound) (tickTraversalEmitter tm kind backward)

theorem tickCoordinateBody_embeds (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool) :
    (tickCoordinateBody tm kind bound backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickOutputPreparationTemplate_embeds tm kind bound)
    (tickTraversalEmitter_embeds tm kind backward)

theorem tickCoordinateBody_run (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool) :
    (tickCoordinateBody tm kind bound backward).Runs := by
  apply sequenceProgramTemplate_run _ _ (tickOutputPreparationTemplate_embeds tm kind bound)
    (tickOutputPreparationTemplate_run tm kind bound)
  exact sharedFixedGuardedEmitter_run _ _ backward

theorem tickCoordinateBody_ready (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    (tickCoordinateBody tm kind bound backward).ready cs := by
  change (cs (.inl 3) = 0 ∧ cs (.inl 5) = 0) ∧
    (tickTraversalEmitter tm kind backward).ready (tickOutputPreparationCounters tm kind bound cs)
  refine ⟨⟨hr.1, hr.2.2.1⟩, ?_⟩
  have h := sharedFixedGuardedEmitter_ready (tickTraversalSupply tm) (tickTreeForKind tm kind)
    (tickOutputPreparationCounters tm kind bound cs) (tickOutputPreparation_ready_preserved tm kind bound cs hr)
  cases backward
  · exact h.1
  · exact h.2

theorem tickCoordinateBody_spare_frame (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (tickCoordinateBody tm kind bound backward).counters cs (tickTraversalSpare tm j) = cs (tickTraversalSpare tm j) := by
  change (tickTraversalEmitter tm kind backward).counters (tickOutputPreparationCounters tm kind bound cs)
    (tickTraversalSpare tm j) = _
  rw [tickTraversalEmitter_spare_frame]
  simp [tickOutputPreparationCounters, tickTraversalSpare]

theorem tickCoordinateBody_payload (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    let i : Fin (cs (.inl 1)) := ⟨cs (.inl 2), hi⟩
    let nodes := (boundedTickFormulaForKind tm (cs (.inl 1)) i kind).paddedCompile
      (fun j => cs (.inl 0) + j.val) (tickPreparedOutputAddress tm kind bound cs) bound
    (tickCoordinateBody tm kind bound backward).bytes cs =
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  let after := tickOutputPreparationCounters tm kind bound cs
  have hz : after (.inl 13) = after (.inl 12) + bound := by simp [after, tickOutputPreparationCounters]
  have hi' : after (.inl 2) < after (.inl 1) := by simpa [after, tickOutputPreparationCounters] using hi
  have h := tickTraversalEmitter_payload tm kind backward after bound hz hi'
  let payload := fun (capacity position : Nat) (hi : position < capacity) =>
    let nodes := (boundedTickFormulaForKind tm capacity ⟨position, hi⟩ kind).paddedCompile
      (fun j => cs (.inl 0) + j.val) (tickPreparedOutputAddress tm kind bound cs) bound
    ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten
  have h0 : after (.inl 0) = cs (.inl 0) := by simp [after, tickOutputPreparationCounters]
  have h12 : after (.inl 12) = tickPreparedOutputAddress tm kind bound cs := by
    simp [after, tickOutputPreparationCounters]
  have he : payload (after (.inl 1)) (after (.inl 2)) hi' =
      payload (cs (.inl 1)) (cs (.inl 2)) hi := by
    congr 1 <;> simp [after, tickOutputPreparationCounters]
  have hh : (tickTraversalEmitter tm kind backward).bytes after =
      payload (after (.inl 1)) (after (.inl 2)) hi' := by
    simpa only [payload, h0, h12] using h
  rw [he] at hh
  simpa only [tickCoordinateBody, sequenceProgramTemplate, tickOutputPreparationTemplate,
    List.append_nil, payload] using hh

theorem tickCoordinateBody_count (tm : Turing.FinTM2) (kind : TickTreeKind tm) (bound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (hi : cs (.inl 2) < cs (.inl 1)) :
    let i : Fin (cs (.inl 1)) := ⟨cs (.inl 2), hi⟩
    (tickCoordinateBody tm kind bound backward).counters cs (.inl 9) =
      cs (.inl 9) + formulaElementaryLayers (boundedTickFormulaForKind tm (cs (.inl 1)) i kind) + 1 := by
  let after := tickOutputPreparationCounters tm kind bound cs
  have hi' : after (.inl 2) < after (.inl 1) := by simpa [after, tickOutputPreparationCounters] using hi
  have h := tickTraversalEmitter_count tm kind backward after hi'
  let count := fun (capacity position : Nat) (hi : position < capacity) =>
    formulaElementaryLayers (boundedTickFormulaForKind tm capacity ⟨position, hi⟩ kind)
  have h9 : after (.inl 9) = cs (.inl 9) := by simp [after, tickOutputPreparationCounters]
  have he : count (after (.inl 1)) (after (.inl 2)) hi' =
      count (cs (.inl 1)) (cs (.inl 2)) hi := by
    congr 1 <;> simp [after, tickOutputPreparationCounters]
  have hh : (tickTraversalEmitter tm kind backward).counters after (.inl 9) =
      cs (.inl 9) + count (after (.inl 1)) (after (.inl 2)) hi' + 1 := by
    simpa only [count, h9] using h
  rw [he] at hh
  simpa only [tickCoordinateBody, sequenceProgramTemplate, tickOutputPreparationTemplate, count] using hh

theorem tickCoordinateBody_polynomial (tm : Turing.FinTM2) (kind : TickTreeKind tm) (strideBound : Nat)
    (backward : Bool) (bound : Polynomial Nat) : (tickCoordinateBody tm kind strideBound backward).PolynomiallyTimed bound := by
  obtain ⟨clock, hc⟩ := tickOutputPreparationSteps_polynomial tm kind strideBound bound
  apply sequenceProgramTemplate_polynomial _ _ bound
    (bound + tickPreparedOutputBudget tm kind strideBound bound + Polynomial.C strideBound)
  · exact ⟨clock, fun n cs hb _ => hc n cs hb⟩
  · intro n cs hb _
    exact tickOutputPreparationCounters_bound tm kind strideBound bound n cs hb
  · exact sharedFixedGuardedEmitter_polynomial _ _ backward _

end ShiReversibleGenerator
