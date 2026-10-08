import ReversibleOutputCopySetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem outputCopySetupTemplate_ready (cs : OutputCopyMasterRegister → Nat) :
    outputCopySetupTemplate.ready cs ↔ cs (.inl 5)=0 := by
  simp [outputCopySetupTemplate,outputCopySetupPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,
    decrementProgramTemplate,cleanupProgramTemplate,AffineAtom.apply]

theorem outputCopySetupTemplate_bytes (cs : OutputCopyMasterRegister → Nat) :
    outputCopySetupTemplate.bytes cs=[] := rfl

/-- Exact runtime pointers and scratch initialization; layer count starts at zero. -/
theorem outputCopySetupTemplate_metadata (cs : OutputCopyMasterRegister → Nat) :
    let final := outputCopySetupTemplate.counters cs
    final (.inr 0)=cs (.inl 10)-1 ∧ final (.inr 1)=cs (.inl 10)+cs (.inl 9)-1 ∧
      final (.inr 5)=cs (.inl 4) ∧ final (.inr 6)=cs (.inl 9) ∧
      final (.inr 2)=0 ∧ final (.inr 3)=0 ∧ final (.inr 4)=0 ∧
      final (.inr 7)=0 ∧ final (.inr 8)=0 ∧ final (.inr 9)=0 := by
  simp [outputCopySetupTemplate,outputCopySetupPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,
    decrementProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,AffineAtom.apply]

theorem outputCopySetupTemplate_prelude_frame (cs : OutputCopyMasterRegister → Nat) (q : WorkspaceRegister) :
    outputCopySetupTemplate.counters cs (.inl q)=cs (.inl q) := by
  simp [outputCopySetupTemplate,outputCopySetupPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,
    decrementProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,AffineAtom.apply]

end ShiReversibleGenerator
