import ReversibleRawLengthPhaseTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R S : Type} [DecidableEq R] [DecidableEq S]

def sharedPhaseRegisterMap (f : R → S) : RawLengthPhaseRegister R → RawLengthPhaseRegister S
  | .inl j => .inl j
  | .inr r => .inr (f r)

theorem sharedPhaseRegisterMap_injective (f : R → S) (hf : Function.Injective f) :
    Function.Injective (sharedPhaseRegisterMap f) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b => exact congrArg Sum.inr (hf (Sum.inr.inj h))

/-- Different finite component register types share the same length/count/scratch block. -/
noncomputable def sharedPhaseLift (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S) :
    CounterProgramTemplate (RawLengthPhaseRegister S) :=
  injectProgramTemplate p (sharedPhaseRegisterMap f) (.inl 0)

theorem sharedPhaseLift_embeds (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S) :
    (sharedPhaseLift p f).Embeds := injectProgramTemplate_embeds _ _ _

theorem sharedPhaseLift_run (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S)
    (hf : Function.Injective f) (he : p.Embeds) (hr : p.Runs) : (sharedPhaseLift p f).Runs :=
  injectProgramTemplate_run _ _ (sharedPhaseRegisterMap_injective f hf) _ he hr

theorem sharedPhaseLift_ready (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S)
    (hp : ∀ cs,cs (.inl 2)=0 → p.ready cs) (cs : RawLengthPhaseRegister S → Nat) (hs : cs (.inl 2)=0) :
    (sharedPhaseLift p f).ready cs := hp _ hs

theorem sharedPhaseLift_pull (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S)
    (hf : Function.Injective f) (cs : RawLengthPhaseRegister S → Nat) (q : RawLengthPhaseRegister R) :
    (sharedPhaseLift p f).counters cs (sharedPhaseRegisterMap f q)=
      p.counters (fun r => cs (sharedPhaseRegisterMap f r)) q :=
  injectedTemplateCounters_pull _ (sharedPhaseRegisterMap_injective f hf) _ _ _

theorem sharedPhaseLift_private_zero (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S)
    (hf : Function.Injective f) (hp : ∀ cs r,p.counters cs (.inr r)=0)
    (cs : RawLengthPhaseRegister S → Nat) (hz : ∀ q,cs (.inr q)=0) :
    ∀ q,(sharedPhaseLift p f).counters cs (.inr q)=0 := by
  classical
  intro q
  by_cases h : ∃ r,f r=q
  · obtain ⟨r,rfl⟩ := h
    exact (sharedPhaseLift_pull p f hf cs (.inr r)).trans (hp _ r)
  · change injectedTemplateCounters (sharedPhaseRegisterMap f) cs
      (p.counters (fun r => cs (sharedPhaseRegisterMap f r))) (.inr q)=0
    rw [injectedTemplateCounters_outside]
    · exact hz q
    · intro r
      cases r with
      | inl j => simp [sharedPhaseRegisterMap]
      | inr r =>
        intro he
        exact h ⟨r,Sum.inr.inj he⟩

theorem sharedPhaseLift_resources (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S)
    (hf : Function.Injective f) (bound : Polynomial Nat) (hb : p.CounterBound bound) (ht : p.PolynomiallyTimed bound) :
    (sharedPhaseLift p f).CounterBound bound ∧ (sharedPhaseLift p f).PolynomiallyTimed bound :=
  ⟨injectProgramTemplate_budget _ _ (sharedPhaseRegisterMap_injective f hf) _ _ hb,
    injectProgramTemplate_polynomial _ _ _ _ ht⟩

end ShiReversibleGenerator
