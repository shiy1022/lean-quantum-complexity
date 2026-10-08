import ReversibleExtractionPaddedRegisterInjection
import ReversibleTemplateRegisterInjectionRun

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The output forest retains its loop count and padding bound outside every initialized padded leaf. -/
abbrev ExtractionForestRegister := Fin 28

def extractionPaddedToForestRegister (r : ExtractionPaddedRegister) : ExtractionForestRegister :=
  ⟨r.val, by have := r.isLt; omega⟩

theorem extractionPaddedToForestRegister_injective :
    Function.Injective extractionPaddedToForestRegister := by
  intro a b h
  have hv := congrArg (fun r : ExtractionForestRegister => r.val) h
  exact Fin.ext hv

noncomputable def extractionForestLift (p : CounterProgramTemplate ExtractionPaddedRegister) :
    CounterProgramTemplate ExtractionForestRegister :=
  injectProgramTemplate p extractionPaddedToForestRegister 2

theorem extractionForestLift_embeds (p : CounterProgramTemplate ExtractionPaddedRegister) :
    (extractionForestLift p).Embeds := injectProgramTemplate_embeds _ _ _

theorem extractionForestLift_run (p : CounterProgramTemplate ExtractionPaddedRegister)
    (he : p.Embeds) (hr : p.Runs) : (extractionForestLift p).Runs :=
  injectProgramTemplate_run _ _ extractionPaddedToForestRegister_injective _ he hr

theorem extractionForestLift_polynomial (p : CounterProgramTemplate ExtractionPaddedRegister)
    (bound : Polynomial Nat) (hp : p.PolynomiallyTimed bound) :
    (extractionForestLift p).PolynomiallyTimed bound :=
  injectProgramTemplate_polynomial _ _ _ _ hp

/-- The added traversal counters are framed by the actual injected counter transition. -/
theorem extractionForestLift_outside (p : CounterProgramTemplate ExtractionPaddedRegister)
    (cs : ExtractionForestRegister → Nat) (q : ExtractionForestRegister) (hq : 26 ≤ q.val) :
    (extractionForestLift p).counters cs q=cs q := by
  apply injectedTemplateCounters_outside
  intro r h
  have hv := congrArg Fin.val h
  have := r.isLt
  simp only [extractionPaddedToForestRegister] at hv
  omega

theorem extractionForestLift_pull (p : CounterProgramTemplate ExtractionPaddedRegister)
    (cs : ExtractionForestRegister → Nat) (r : ExtractionPaddedRegister) :
    (extractionForestLift p).counters cs (extractionPaddedToForestRegister r)=
      p.counters (fun s => cs (extractionPaddedToForestRegister s)) r :=
  injectedTemplateCounters_pull _ extractionPaddedToForestRegister_injective _ _ _

end ShiReversibleGenerator
