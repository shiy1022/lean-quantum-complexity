import ReversibleOutputCopyMasterPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- A single finite program establishes the copy metadata, emits the padded-root CNOT circuit,
counts its layers, and preserves the resource prelude, with an actual polynomial instruction clock. -/
theorem outputCopyMasterTemplate_circuit_certificate (budget : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : OutputCopyMasterRegister → Nat),
      (∀ q,cs q ≤ budget.eval n) → cs (.inl 5)=0 →
      ∀ (L : Type) (caller : L → CounterInstr OutputCopyMasterRegister L) (stop : L) (ys : List Bool)
        (wires sourceBase : Nat) (hstride : 0 < cs (.inl 4)) (hend : 0 < cs (.inl 10))
        (hroot : sourceBase+cs (.inl 9)*cs (.inl 4)=cs (.inl 10))
        (hout : cs (.inl 10)+cs (.inl 9) ≤ wires),
      let gs := stridedOutputCopyLayers wires sourceBase (cs (.inl 4)) (cs (.inl 10))
        (cs (.inl 9)) hstride (by omega) hout
      CounterRun (outputCopyMasterTemplate.code caller stop)
        ⟨some (outputCopyMasterTemplate.entry stop),cs,ys⟩ (outputCopyMasterTemplate.steps cs)
        ⟨some (outputCopyMasterTemplate.exit stop),outputCopyMasterTemplate.counters cs,
          (gs.map ShiBQP.encLayer).flatten++ys⟩ ∧
      outputCopyMasterTemplate.steps cs ≤ clock.eval n ∧
      outputCopyMasterTemplate.counters cs (.inr 2)=cs (.inl 9) ∧
      outputCopyMasterTemplate.counters cs (.inr 6)=0 ∧
      ∀ q,outputCopyMasterTemplate.counters cs (.inl q)=cs (.inl q) := by
  obtain ⟨clock,hclock⟩ := outputCopyMasterTemplate_polynomial budget
  refine ⟨clock,?_⟩
  intro n cs hb hscratch L caller stop ys wires sourceBase hstride hend hroot hout
  dsimp only
  have hr := (outputCopyMasterTemplate_ready cs).2 hscratch
  have hrun := outputCopyMasterTemplate_run L caller stop cs ys hr
  rw [outputCopyMasterTemplate_strided_payload cs wires sourceBase hstride hend hroot hout] at hrun
  obtain ⟨hc,he⟩ := outputCopyMasterTemplate_counts cs
  exact ⟨hrun,hclock n cs hb hr,hc,he,outputCopyMasterTemplate_prelude_frame cs⟩

end ShiReversibleGenerator
