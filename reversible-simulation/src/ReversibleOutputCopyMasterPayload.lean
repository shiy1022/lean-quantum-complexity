import ReversibleOutputCopyMasterTemplate
import ReversibleOutputCopyStridedLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Setup and the injected traversal emit the exact quantum copy circuit from runtime metadata. -/
theorem outputCopyMasterTemplate_quantum_payload (cs : OutputCopyMasterRegister → Nat)
    (wires : Nat) (hend : 0 < cs (.inl 10))
    (hout : cs (.inl 10)+cs (.inl 9) ≤ wires) :
    outputCopyMasterTemplate.bytes cs=
      ((outputCopyQuantumLayers wires (cs (.inl 10)) (cs (.inl 4))
        (cs (.inl 9)) (cs (.inl 10)-1) (by omega) hout).map ShiBQP.encLayer).flatten := by
  obtain ⟨h0,h1,h5,h6,h2,h3,h4,h7,h8,h9⟩ := outputCopySetupTemplate_metadata cs
  change outputCopyLoopTemplate.bytes (fun q => outputCopySetupTemplate.counters cs (.inr q)) ++ [] = _
  rw [List.append_nil,outputCopyLoopTemplate_quantum_payload
    (fun q => outputCopySetupTemplate.counters cs (.inr q)) wires (cs (.inl 10))
    (by simpa only [h0] using (show cs (.inl 10)-1 < cs (.inl 10) by omega))
    (by simpa only [h6] using hout) (by rw [h1,h6])]
  simp only [h0,h5,h6]

/-- The real layer counter records the output width, and the traversal counter is exhausted. -/
theorem outputCopyMasterTemplate_counts (cs : OutputCopyMasterRegister → Nat) :
    outputCopyMasterTemplate.counters cs (.inr 2)=cs (.inl 9) ∧
      outputCopyMasterTemplate.counters cs (.inr 6)=0 := by
  obtain ⟨h0,h1,h5,h6,h2,h3,h4,h7,h8,h9⟩ := outputCopySetupTemplate_metadata cs
  obtain ⟨_,_,hc,_,hr⟩ := outputCopyLoopTemplate_pointer_count_result
    (fun q => outputCopySetupTemplate.counters cs (.inr q))
  change injectedTemplateCounters Sum.inr _ _ (.inr 2)=_ ∧
    injectedTemplateCounters Sum.inr _ _ (.inr 6)=_
  rw [injectedTemplateCounters_pull Sum.inr (by intro a b h; cases h; rfl),
    injectedTemplateCounters_pull Sum.inr (by intro a b h; cases h; rfl),hc,hr,h2,h6]
  simp

/-- Copy emission leaves the resource prelude available for subsequent generator stages. -/
theorem outputCopyMasterTemplate_prelude_frame (cs : OutputCopyMasterRegister → Nat)
    (q : WorkspaceRegister) : outputCopyMasterTemplate.counters cs (.inl q)=cs (.inl q) := by
  change injectedTemplateCounters Sum.inr _ _ (.inl q)=_
  rw [injectedTemplateCounters_outside Sum.inr _ _ (.inl q) (by intro r; simp)]
  exact outputCopySetupTemplate_prelude_frame cs q

/-- The generated circuit agrees with the padded extraction roots in increasing output order. -/
theorem outputCopyMasterTemplate_strided_payload (cs : OutputCopyMasterRegister → Nat)
    (wires sourceBase : Nat) (hstride : 0 < cs (.inl 4)) (hend : 0 < cs (.inl 10))
    (hroot : sourceBase+cs (.inl 9)*cs (.inl 4)=cs (.inl 10))
    (hout : cs (.inl 10)+cs (.inl 9) ≤ wires) :
    outputCopyMasterTemplate.bytes cs=
      ((stridedOutputCopyLayers wires sourceBase (cs (.inl 4)) (cs (.inl 10))
        (cs (.inl 9)) hstride (by omega) hout).map ShiBQP.encLayer).flatten := by
  rw [outputCopyMasterTemplate_quantum_payload cs wires hend hout]
  have h := outputCopyQuantumLayers_strided wires sourceBase (cs (.inl 4)) (cs (.inl 10))
    (cs (.inl 9)) hstride hend (by omega) hout
  simpa only [hroot] using congrArg (fun gs => (gs.map ShiBQP.encLayer).flatten) h

end ShiReversibleGenerator
