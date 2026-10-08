import ReversibleOutputCopySetupClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

noncomputable def outputCopyMasterTemplate : CounterProgramTemplate OutputCopyMasterRegister :=
  sequenceProgramTemplate outputCopySetupTemplate
    (injectProgramTemplate outputCopyLoopTemplate Sum.inr 0)

theorem outputCopyMasterTemplate_embeds : outputCopyMasterTemplate.Embeds :=
  sequenceProgramTemplate_embeds _ _ outputCopySetupTemplate_embeds
    (injectProgramTemplate_embeds _ _ _)

theorem outputCopyMasterTemplate_run : outputCopyMasterTemplate.Runs :=
  sequenceProgramTemplate_run _ _ outputCopySetupTemplate_embeds outputCopySetupTemplate_run
    (injectProgramTemplate_run _ _ (by intro a b h; cases h; rfl) 0
      outputCopyLoopTemplate_embeds outputCopyLoopTemplate_run)

/-- Setup actually establishes the loop's scratch invariants from the real prelude scratch register. -/
theorem outputCopyMasterTemplate_ready (cs : OutputCopyMasterRegister → Nat) :
    outputCopyMasterTemplate.ready cs ↔ cs (.inl 5)=0 := by
  change (outputCopySetupTemplate.ready cs ∧ _) ↔ _
  constructor
  · intro h
    exact (outputCopySetupTemplate_ready cs).1 h.1
  · intro hs
    obtain ⟨h0,h1,h5,h6,h2,h3,h4,h7,h8,h9⟩ := outputCopySetupTemplate_metadata cs
    refine ⟨(outputCopySetupTemplate_ready cs).2 hs,?_⟩
    exact outputCopyLoopTemplate_ready (fun q => outputCopySetupTemplate.counters cs (.inr q)) h3 h4

/-- The actual setup, continuation bridge, and copy traversal together run in polynomial time. -/
theorem outputCopyMasterTemplate_polynomial (bound : Polynomial Nat) :
    outputCopyMasterTemplate.PolynomiallyTimed bound :=
  sequenceProgramTemplate_polynomial _ _ bound (Polynomial.C 2*bound)
    (outputCopySetupTemplate_polynomial bound)
    (by
      intro n cs hb hr q
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using outputCopySetupTemplate_uniform_bound cs (bound.eval n) hb q)
    (injectProgramTemplate_polynomial _ _ _ _ (outputCopyLoopTemplate_polynomial (Polynomial.C 2*bound)))

end ShiReversibleGenerator
