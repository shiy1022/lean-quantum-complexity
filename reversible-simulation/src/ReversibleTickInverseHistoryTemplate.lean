import ReversibleTickInitializedWindowClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Preserve the full time budget in spare7 and copy the remaining regular tick count to spare3. -/
noncomputable def tickHistoryCountTemplate (tm : Turing.FinTM2) :=
  counterAffineCopyProgramTemplate (tickTraversalSpare tm 7) (tickTraversalSpare tm 3) (.inl 5) 0 1 1

/-- The initialized boundary tick has stride18; all later ticks use the regular padded stride. -/
noncomputable def tickInverseHistoryTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  sequenceProgramTemplate (tickHistoryCountTemplate tm)
    (sequenceProgramTemplate (tickInverseAdvanceStepTemplate tm 18 bound)
      (tickInverseAdvanceIterationTemplate tm bound))

theorem tickHistoryCountTemplate_embeds (tm : Turing.FinTM2) : (tickHistoryCountTemplate tm).Embeds :=
  counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _

theorem tickHistoryCountTemplate_run (tm : Turing.FinTM2) : (tickHistoryCountTemplate tm).Runs := by
  apply counterAffineCopyProgramTemplate_run
  · exact fun h => (by decide : (7 : Fin 8) ≠ 3) (tickTraversalSpare_injective tm h)
  · simp [tickTraversalSpare]
  · simp [tickTraversalSpare]

theorem tickHistoryCountTemplate_counters (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickHistoryCountTemplate tm).counters cs=
      Function.update cs (tickTraversalSpare tm 3) (cs (tickTraversalSpare tm 7)-1) := by
  simp only [tickHistoryCountTemplate,counterAffineCopyProgramTemplate,Nat.one_mul,Nat.add_zero]

theorem tickHistoryCountTemplate_polynomial (tm : Turing.FinTM2) (budget : Polynomial Nat) :
    (tickHistoryCountTemplate tm).PolynomiallyTimed budget :=
  counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ budget

theorem tickInverseHistoryTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickInverseHistoryTemplate tm bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickHistoryCountTemplate_embeds tm)
    (sequenceProgramTemplate_embeds _ _ (tickInverseAdvanceStepTemplate_embeds tm 18 bound)
      (tickInverseAdvanceIterationTemplate_embeds tm bound))

theorem tickInverseHistoryTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickInverseHistoryTemplate tm bound).Runs :=
  sequenceProgramTemplate_run _ _ (tickHistoryCountTemplate_embeds tm) (tickHistoryCountTemplate_run tm)
    (sequenceProgramTemplate_run _ _ (tickInverseAdvanceStepTemplate_embeds tm 18 bound)
      (tickInverseAdvanceStepTemplate_run tm 18 bound) (tickInverseAdvanceIterationTemplate_run tm bound))

end ShiReversibleGenerator
