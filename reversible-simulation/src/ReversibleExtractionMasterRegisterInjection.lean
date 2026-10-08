import ReversibleExtractionForestCircuitCertificate
import ReversibleWorkspaceOffsets
import ReversibleTemplateRegisterInjectionRun

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Keep resource metadata separate from the scratch-clean extraction forest. -/
abbrev ExtractionMasterRegister := WorkspaceRegister ⊕ ExtractionForestRegister

noncomputable def extractionMasterLift (p : CounterProgramTemplate ExtractionForestRegister) :
    CounterProgramTemplate ExtractionMasterRegister := injectProgramTemplate p Sum.inr 2

theorem extractionMasterLift_embeds (p : CounterProgramTemplate ExtractionForestRegister) :
    (extractionMasterLift p).Embeds := injectProgramTemplate_embeds _ _ _

theorem extractionMasterLift_run (p : CounterProgramTemplate ExtractionForestRegister)
    (he : p.Embeds) (hr : p.Runs) : (extractionMasterLift p).Runs :=
  injectProgramTemplate_run _ _ (by intro a b h; exact Sum.inr.inj h) _ he hr

theorem extractionMasterLift_polynomial (p : CounterProgramTemplate ExtractionForestRegister)
    (bound : Polynomial Nat) (hp : p.PolynomiallyTimed bound) :
    (extractionMasterLift p).PolynomiallyTimed bound := injectProgramTemplate_polynomial _ _ _ _ hp

theorem extractionMasterLift_pull (p : CounterProgramTemplate ExtractionForestRegister)
    (cs : ExtractionMasterRegister → Nat) (r : ExtractionForestRegister) :
    (extractionMasterLift p).counters cs (.inr r)=p.counters (fun q => cs (.inr q)) r :=
  injectedTemplateCounters_pull _ (by intro a b h; exact Sum.inr.inj h) _ _ _

theorem extractionMasterLift_workspace (p : CounterProgramTemplate ExtractionForestRegister)
    (cs : ExtractionMasterRegister → Nat) (r : WorkspaceRegister) :
    (extractionMasterLift p).counters cs (.inl r)=cs (.inl r) :=
  injectedTemplateCounters_outside _ _ _ _ (by intro q; simp)

theorem extractionMasterLift_budget (p : CounterProgramTemplate ExtractionForestRegister)
    (bound : Polynomial Nat) (hp : p.CounterBound bound) : (extractionMasterLift p).CounterBound bound := by
  obtain ⟨budget,hbudget⟩ := hp
  refine ⟨budget+bound,?_⟩
  intro n cs hb q
  simp only [Polynomial.eval_add]
  cases q with
  | inl r => rw [extractionMasterLift_workspace]; exact (hb _).trans (by omega)
  | inr r => rw [extractionMasterLift_pull]; exact (hbudget n _ (fun z => hb _) r).trans (by omega)

end ShiReversibleGenerator
