import ReversibleCoordinateBindingProgramTemplate
import ReversibleExtractionIndexSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def extractionInputBindingRegisters (position target : ExtractionTermRegister) :
    CoordinateBindingRegisters ExtractionTermRegister := ⟨11,0,position,8,target,7⟩

noncomputable def extractionFirstSymbol (tm : Turing.FinTM2) : Option (MachineSymbol tm) :=
  (Fintype.equivFin (Option (MachineSymbol tm))).symm ⟨0,Fintype.card_pos⟩

/-- Three fixed binders use the actual runtime predecessor/current/payload indices. -/
noncomputable def extractionInputBindingTemplate (tm : Turing.FinTM2) (stride : Nat) :=
  sequenceProgramTemplate
    (coordinateBindingProgramTemplate tm (extractionInputBindingRegisters 10 19) stride
      (.inr ((tm.k₁,.position),none)))
    (sequenceProgramTemplate
      (coordinateBindingProgramTemplate tm (extractionInputBindingRegisters 2 20) stride
        (.inr ((tm.k₁,.position),none)))
      (coordinateBindingProgramTemplate tm (extractionInputBindingRegisters 4 21) stride
        (.inr ((tm.k₁,.position),extractionFirstSymbol tm))))

noncomputable def extractionBoundInputs (tm : Turing.FinTM2) (stride : Nat) :
    ExtractionTermInput tm → SymbolicWire ExtractionTermRegister
  | .inl i => ⟨if i.val=0 then 19 else 20,0⟩
  | .inr a => ⟨21,((Fintype.equivFin (Option (MachineSymbol tm))) a).val*stride⟩

theorem extractionBoundInputs_stable (tm : Turing.FinTM2) (stride : Nat) :
    ∀ i,extractionTermNodeRegisters.SourceStable (extractionBoundInputs tm stride i).source := by
  intro i
  cases i with
  | inl i =>
    simp [extractionBoundInputs,extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]
    split_ifs <;> decide
  | inr a => simp [extractionBoundInputs,extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]

theorem extractionInputBindingTemplate_embeds (tm : Turing.FinTM2) (stride : Nat) :
    (extractionInputBindingTemplate tm stride).Embeds := by
  unfold extractionInputBindingTemplate
  repeat' first
    | apply sequenceProgramTemplate_embeds
    | apply coordinateBindingProgramTemplate_embeds

theorem extractionInputBindingTemplate_run (tm : Turing.FinTM2) (stride : Nat) :
    (extractionInputBindingTemplate tm stride).Runs := by
  unfold extractionInputBindingTemplate
  repeat' first
    | apply sequenceProgramTemplate_run
    | apply sequenceProgramTemplate_embeds
    | apply coordinateBindingProgramTemplate_embeds
    | apply coordinateBindingProgramTemplate_run
    | (constructor <;> decide)

theorem extractionInputBindingTemplate_ready (tm : Turing.FinTM2) (stride : Nat)
    (cs : ExtractionTermRegister → Nat) (h8 : cs 8=0) (h7 : cs 7=0) :
    (extractionInputBindingTemplate tm stride).ready cs := by
  simp [extractionInputBindingTemplate,sequenceProgramTemplate,coordinateBindingProgramTemplate,
    extractionInputBindingRegisters,h8,h7]

end ShiReversibleGenerator
