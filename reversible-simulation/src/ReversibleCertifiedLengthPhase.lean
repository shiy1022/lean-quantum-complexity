import ReversibleSharedPhaseRegisterLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R S : Type} [DecidableEq R] [DecidableEq S]

/-- Actual finite phases expose exactly the shared data needed by family assembly. -/
structure CertifiedLengthPhase (R : Type) [DecidableEq R] where
  program : CounterProgramTemplate (RawLengthPhaseRegister R)
  payload : Nat → List Bool
  layers : Nat → Nat
  embeds : program.Embeds
  runs : program.Runs
  ready : ∀ cs,cs (.inl 2)=0 → program.ready cs
  bytes : ∀ cs,program.bytes cs=payload (cs (.inl 0))
  total : ∀ cs,program.counters cs (.inl 1)=cs (.inl 1)+layers (cs (.inl 0))
  length : ∀ cs,program.counters cs (.inl 0)=cs (.inl 0)
  scratch : ∀ cs,program.counters cs (.inl 2)=cs (.inl 2)
  privateZero : ∀ cs,(∀ r,cs (.inr r)=0) → ∀ r,program.counters cs (.inr r)=0
  resources : ∀ bound : Polynomial Nat,program.CounterBound bound ∧ program.PolynomiallyTimed bound

theorem sharedPhaseLift_private_zero_at (p : CounterProgramTemplate (RawLengthPhaseRegister R)) (f : R → S)
    (hf : Function.Injective f) (cs : RawLengthPhaseRegister S → Nat)
    (hp : ∀ r,p.counters (fun q => cs (sharedPhaseRegisterMap f q)) (.inr r)=0)
    (hz : ∀ q,cs (.inr q)=0) : ∀ q,(sharedPhaseLift p f).counters cs (.inr q)=0 := by
  classical
  intro q
  by_cases h : ∃ r,f r=q
  · obtain ⟨r,rfl⟩ := h
    exact (sharedPhaseLift_pull p f hf cs (.inr r)).trans (hp r)
  · change injectedTemplateCounters (sharedPhaseRegisterMap f) cs
      (p.counters (fun r => cs (sharedPhaseRegisterMap f r))) (.inr q)=0
    rw [injectedTemplateCounters_outside]
    · exact hz q
    · intro r
      cases r with
      | inl j => simp [sharedPhaseRegisterMap]
      | inr r => intro he; exact h ⟨r,Sum.inr.inj he⟩

noncomputable def CertifiedLengthPhase.lift (a : CertifiedLengthPhase R) (f : R → S)
    (hf : Function.Injective f) : CertifiedLengthPhase S where
  program := sharedPhaseLift a.program f
  payload := a.payload
  layers := a.layers
  embeds := sharedPhaseLift_embeds _ _
  runs := sharedPhaseLift_run _ _ hf a.embeds a.runs
  ready := sharedPhaseLift_ready _ _ a.ready
  bytes := fun cs => a.bytes (fun q => cs (sharedPhaseRegisterMap f q))
  total := fun cs => (sharedPhaseLift_pull _ _ hf cs (.inl 1)).trans (a.total _)
  length := fun cs => (sharedPhaseLift_pull _ _ hf cs (.inl 0)).trans (a.length _)
  scratch := fun cs => (sharedPhaseLift_pull _ _ hf cs (.inl 2)).trans (a.scratch _)
  privateZero := fun cs hz => sharedPhaseLift_private_zero_at _ _ hf cs
    (a.privateZero _ (fun r => hz (f r))) hz
  resources := fun bound => sharedPhaseLift_resources _ _ hf bound (a.resources bound).1 (a.resources bound).2

end ShiReversibleGenerator
