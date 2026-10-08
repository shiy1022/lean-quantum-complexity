import ReversibleOutputCopySetupMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- All copied addresses fit twice the original metadata/counter bound. -/
theorem outputCopySetupTemplate_uniform_bound (cs : OutputCopyMasterRegister → Nat) (bound : Nat)
    (hb : ∀ q,cs q ≤ bound) : ∀ q,outputCopySetupTemplate.counters cs q ≤ 2*bound := by
  intro q
  cases q with
  | inl r =>
      rw [outputCopySetupTemplate_prelude_frame]
      have h := hb (.inl r)
      omega
  | inr r =>
      have h10 := hb (.inl 10)
      have h9 := hb (.inl 9)
      have h4 := hb (.inl 4)
      fin_cases r
      all_goals simp [outputCopySetupTemplate,outputCopySetupPrograms,listProgramTemplate,identityProgramTemplate,
        sequenceProgramTemplate,counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,
        decrementProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,AffineAtom.apply]
      all_goals omega

/-- The finite arithmetic/cleanup setup has an actual instruction bound, including every clear and copy. -/
theorem outputCopySetupTemplate_polynomial (bound : Polynomial Nat) : outputCopySetupTemplate.PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 55*bound+Polynomial.C 22,?_⟩
  intro n cs hb _
  have h10 := hb (.inl 10)
  have h9 := hb (.inl 9)
  have h4 := hb (.inl 4)
  have h0 := hb (.inr 0)
  have h1 := hb (.inr 1)
  have h2 := hb (.inr 2)
  have h3 := hb (.inr 3)
  have htmp := hb (.inr 4)
  have h5 := hb (.inr 5)
  have h6 := hb (.inr 6)
  have h7 := hb (.inr 7)
  have h8 := hb (.inr 8)
  have hx := hb (.inr 9)
  simp [outputCopySetupTemplate,outputCopySetupPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,
    decrementProgramTemplate,cleanupProgramTemplate,cleanupSteps,cleanupCounters_apply,AffineAtom.apply,
    AffineAtom.steps,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
