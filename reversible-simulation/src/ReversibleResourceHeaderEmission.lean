import ReversibleResourceHeaderAdministrationResources
import ReversibleFamilyHeaderProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def resourceHeaderEmissionTemplate : CounterProgramTemplate ResourceHeaderRegister :=
  familyHeaderProgramTemplate (.inr 12) (.inr 10) (.inr 13) (.inr 6) (.inr 5)

theorem resourceHeaderEmissionTemplate_embeds : resourceHeaderEmissionTemplate.Embeds :=
  familyHeaderProgramTemplate_embeds _ _ _ _ _

theorem resourceHeaderEmissionTemplate_run : resourceHeaderEmissionTemplate.Runs := by
  apply familyHeaderProgramTemplate_run <;> simp

theorem resourceHeaderEmissionTemplate_resources (bound : Polynomial Nat) :
    resourceHeaderEmissionTemplate.CounterBound bound ∧ resourceHeaderEmissionTemplate.PolynomiallyTimed bound :=
  familyHeaderProgramTemplate_resources _ _ _ _ _ bound

theorem workspaceResult_outputWidth (tm : Turing.FinTM2) (n budget : Nat) :
    operationResult (workspaceOperations tm) (workspaceInitial tm n budget) 9=
      2*(n+budget*machinePushBound tm+1)+1 := by
  simp [operationResult,workspaceOperations,GeneratorOperation.apply,AffineAtom.apply,workspaceInitial]

/-- The checked prelude's metadata yields the exact established ancilla, output and depth header. -/
theorem resourceHeaderEmissionTemplate_afterAdministration (tm : Turing.FinTM2) (n budget : Nat)
    (cs : ResourceHeaderRegister → Nat)
    (hc : ∀ r,cs (.inr r)=operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r) :
    resourceHeaderEmissionTemplate.ready (resourceHeaderAdministrationTemplate.counters cs) ∧
      resourceHeaderEmissionTemplate.bytes (resourceHeaderAdministrationTemplate.counters cs)=
        ShiBQP.encNat (paddedMachineWorkspace tm n budget+(2*(n+budget*machinePushBound tm+1)+1)-1)++
          ShiBQP.encNat (n+paddedMachineWorkspace tm n budget)++ShiBQP.encNat (cs (.inl 1)) := by
  rw [resourceHeaderAdministrationTemplate_counters]
  constructor
  · change _=0 ∧ _=0
    constructor
    · simpa [Function.update_apply,hc 6] using workspaceResult_buffer tm n budget
    · simpa [Function.update_apply,hc 5] using workspaceResult_scratch tm n budget
  · rw [resourceHeaderEmissionTemplate,familyHeaderProgramTemplate_bytes]
    simp only [Function.update_apply]
    simp [hc 7,hc 9,hc 10,workspaceResult_workspace,workspaceResult_outputWidth,workspaceResult_output]

end ShiReversibleGenerator
