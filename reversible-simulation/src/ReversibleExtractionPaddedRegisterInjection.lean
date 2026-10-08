import ReversibleExtractionTraversalRegisterInjection
import ReversibleTemplateRegisterInjectionRun

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The padded leaf retains a slot root and runtime slot bound outside its traversal registers. -/
abbrev ExtractionPaddedRegister := Fin 26

def extractionTraversalToPaddedRegister (r : ExtractionTraversalRegister) : ExtractionPaddedRegister :=
  ⟨r.val, by have := r.isLt; omega⟩

theorem extractionTraversalToPaddedRegister_injective :
    Function.Injective extractionTraversalToPaddedRegister := by
  intro a b h
  have hv := congrArg (fun r : ExtractionPaddedRegister => r.val) h
  exact Fin.ext hv

noncomputable def extractionPaddedLift (p : CounterProgramTemplate ExtractionTraversalRegister) :
    CounterProgramTemplate ExtractionPaddedRegister :=
  injectProgramTemplate p extractionTraversalToPaddedRegister 2

theorem extractionPaddedLift_embeds (p : CounterProgramTemplate ExtractionTraversalRegister) :
    (extractionPaddedLift p).Embeds := injectProgramTemplate_embeds _ _ _

theorem extractionPaddedLift_run (p : CounterProgramTemplate ExtractionTraversalRegister)
    (he : p.Embeds) (hr : p.Runs) : (extractionPaddedLift p).Runs :=
  injectProgramTemplate_run _ _ extractionTraversalToPaddedRegister_injective _ he hr

theorem extractionPaddedLift_polynomial (p : CounterProgramTemplate ExtractionTraversalRegister)
    (bound : Polynomial Nat) (hp : p.PolynomiallyTimed bound) :
    (extractionPaddedLift p).PolynomiallyTimed bound :=
  injectProgramTemplate_polynomial _ _ _ _ hp

/-- The added traversal counters are framed by the actual injected counter transition. -/
theorem extractionPaddedLift_outside (p : CounterProgramTemplate ExtractionTraversalRegister)
    (cs : ExtractionPaddedRegister → Nat) (q : ExtractionPaddedRegister) (hq : 24 ≤ q.val) :
    (extractionPaddedLift p).counters cs q=cs q := by
  apply injectedTemplateCounters_outside
  intro r h
  have hv := congrArg Fin.val h
  have := r.isLt
  simp only [extractionTraversalToPaddedRegister] at hv
  omega

theorem extractionPaddedLift_pull (p : CounterProgramTemplate ExtractionTraversalRegister)
    (cs : ExtractionPaddedRegister → Nat) (r : ExtractionTraversalRegister) :
    (extractionPaddedLift p).counters cs (extractionTraversalToPaddedRegister r)=
      p.counters (fun s => cs (extractionTraversalToPaddedRegister s)) r :=
  injectedTemplateCounters_pull _ extractionTraversalToPaddedRegister_injective _ _ _

end ShiReversibleGenerator
