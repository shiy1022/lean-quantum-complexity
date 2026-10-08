import ReversibleExtractionTermNegationPrinter
import ReversibleTemplateRegisterInjectionRun

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The traversal owns two counters outside every term-printer scratch register. -/
abbrev ExtractionTraversalRegister := Fin 24

def extractionTermToTraversalRegister (r : ExtractionTermRegister) : ExtractionTraversalRegister :=
  ⟨r.val, by have := r.isLt; omega⟩

theorem extractionTermToTraversalRegister_injective :
    Function.Injective extractionTermToTraversalRegister := by
  intro a b h
  have hv := congrArg (fun r : ExtractionTraversalRegister => r.val) h
  exact Fin.ext hv

noncomputable def extractionTraversalLift (p : CounterProgramTemplate ExtractionTermRegister) :
    CounterProgramTemplate ExtractionTraversalRegister :=
  injectProgramTemplate p extractionTermToTraversalRegister 2

theorem extractionTraversalLift_embeds (p : CounterProgramTemplate ExtractionTermRegister) :
    (extractionTraversalLift p).Embeds := injectProgramTemplate_embeds _ _ _

theorem extractionTraversalLift_run (p : CounterProgramTemplate ExtractionTermRegister)
    (he : p.Embeds) (hr : p.Runs) : (extractionTraversalLift p).Runs :=
  injectProgramTemplate_run _ _ extractionTermToTraversalRegister_injective _ he hr

theorem extractionTraversalLift_polynomial (p : CounterProgramTemplate ExtractionTermRegister)
    (bound : Polynomial Nat) (hp : p.PolynomiallyTimed bound) :
    (extractionTraversalLift p).PolynomiallyTimed bound :=
  injectProgramTemplate_polynomial _ _ _ _ hp

/-- The added traversal counters are framed by the actual injected counter transition. -/
theorem extractionTraversalLift_outside (p : CounterProgramTemplate ExtractionTermRegister)
    (cs : ExtractionTraversalRegister → Nat) (q : ExtractionTraversalRegister) (hq : 22 ≤ q.val) :
    (extractionTraversalLift p).counters cs q=cs q := by
  apply injectedTemplateCounters_outside
  intro r h
  have hv := congrArg Fin.val h
  have := r.isLt
  simp only [extractionTermToTraversalRegister] at hv
  omega

theorem extractionTraversalLift_pull (p : CounterProgramTemplate ExtractionTermRegister)
    (cs : ExtractionTraversalRegister → Nat) (r : ExtractionTermRegister) :
    (extractionTraversalLift p).counters cs (extractionTermToTraversalRegister r)=
      p.counters (fun s => cs (extractionTermToTraversalRegister s)) r :=
  injectedTemplateCounters_pull _ extractionTermToTraversalRegister_injective _ _ _

end ShiReversibleGenerator
