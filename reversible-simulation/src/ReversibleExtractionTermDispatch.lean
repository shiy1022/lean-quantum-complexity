import ReversibleExtractionTermPrinter
import ReversibleCounterAffineProgramTemplates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

abbrev ExtractionTermRegister := Fin 22

noncomputable def extractionTermNodeRegisters : NodePrinterRegisters ExtractionTermRegister :=
  ⟨13,14,15,16,17,7⟩

noncomputable def extractionTermGuardRegisters (a b : ExtractionTermRegister) : GuardProgramRegisters ExtractionTermRegister :=
  ⟨a,b,5,6,7⟩

noncomputable def extractionTermValueDispatch (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister) :
    CounterProgramTemplate ExtractionTermRegister :=
  let leaf := fun value => extractionTermPrinterTemplate tm e backward first endpoint value inputs 18 extractionTermNodeRegisters
  guardedProgramTemplate (extractionTermGuardRegisters 2 1) ⟨.add .position 1,.capacity⟩ (leaf .one)
    (guardedProgramTemplate (extractionTermGuardRegisters 2 1) ⟨.add .capacity 1,.position⟩
      (guardedProgramTemplate (extractionTermGuardRegisters 3 1) ⟨.position,.capacity⟩ (leaf .payload) (leaf .zero))
      (leaf .zero))

noncomputable def extractionTermEndpointDispatch (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister) :
    CounterProgramTemplate ExtractionTermRegister :=
  guardedProgramTemplate (extractionTermGuardRegisters 0 2) ⟨.capacity,.position⟩
    (extractionTermValueDispatch tm e backward first true inputs)
    (extractionTermValueDispatch tm e backward first false inputs)

noncomputable def extractionTermDispatchTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister) :
    CounterProgramTemplate ExtractionTermRegister :=
  sequenceProgramTemplate (counterAffineCopyProgramTemplate 2 3 7 0 2 0)
    (guardedProgramTemplate (extractionTermGuardRegisters 2 1) ⟨.capacity,.literal 0⟩
      (extractionTermEndpointDispatch tm e backward true inputs)
      (extractionTermEndpointDispatch tm e backward false inputs))

/-- All runtime guard branches are fixed finite instruction graphs. -/
theorem extractionTermDispatchTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister) :
    (extractionTermDispatchTemplate tm e backward inputs).Embeds := by
  unfold extractionTermDispatchTemplate
  apply sequenceProgramTemplate_embeds
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · unfold extractionTermEndpointDispatch extractionTermValueDispatch
    repeat' first | apply guardedProgramTemplate_embeds | apply extractionTermPrinterTemplate_embeds

/-- The computed doubled length and every interval test are actual instructions before the selected term printer. -/
theorem extractionTermDispatchTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (hi : ∀ i,extractionTermNodeRegisters.SourceStable (inputs i).source) :
    (extractionTermDispatchTemplate tm e backward inputs).Runs := by
  have leaf : ∀ first endpoint value,
      (extractionTermPrinterTemplate tm e backward first endpoint value inputs 18 extractionTermNodeRegisters).Runs := by
    intro first endpoint value
    exact extractionTermPrinterTemplate_run tm e backward first endpoint value inputs 18 extractionTermNodeRegisters
      (by simp [extractionTermNodeRegisters,NodePrinterRegisters.Valid])
      (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]) hi
  unfold extractionTermDispatchTemplate
  apply sequenceProgramTemplate_run
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide)
  · unfold extractionTermEndpointDispatch extractionTermValueDispatch
    repeat' first
      | exact leaf _ _ _
      | apply guardedProgramTemplate_run
      | apply guardedProgramTemplate_embeds
      | apply extractionTermPrinterTemplate_embeds
      | (constructor <;> decide)

end ShiReversibleGenerator
