import ReversibleExtractionTermDispatchCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual finite runtime dispatch prints the original selected extraction term's raw compiler bytes,
once its finite input registers are bound to the concrete configuration addresses. -/
theorem extractionTermDispatchTemplate_selected_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0)
    (hi : ∀ i,extractionTermNodeRegisters.SourceStable (inputs i).source)
    (read : NaturalConfigurationBit tm → Nat)
    (hinputs : ∀ i,(inputs i).eval (Function.update cs 3 (2*cs 2))=
      read (extractionTermNaturalInput tm (cs 2) (cs 1) i)) :
    (extractionTermDispatchTemplate tm e backward inputs).bytes cs=
      let p := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
      let nodes := p.rawCompile (fun i => read (naturalInputAddress tm (cs 0) i)) (cs 18)
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  rw [extractionTermDispatchTemplate_payload]
  rw [extractionTermPrinterTemplate_payload tm e backward _ _ _ inputs 18 extractionTermNodeRegisters
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]) hi]
  have hag := congrArg (fun p => p.rawCompile read (cs 18))
    (extractionTermSchema_agreement tm e (cs 0) (cs 2) (cs 1) hell)
  simp only [Formula.rename_rawCompile] at hag
  have hre : (fun i => (inputs i).eval (Function.update cs 3 (2*cs 2)))=
      (fun i => read (extractionTermNaturalInput tm (cs 2) (cs 1) i)) := funext hinputs
  dsimp only
  rw [Function.update_of_ne (by decide : (18 : ExtractionTermRegister) ≠ 3),hre,hag]

end ShiReversibleGenerator
