import ReversibleTickPreparedInverseHistoryTemplate
import ReversibleProgramTemplateCountedPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickResourceInverseSetupTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (tickMetadataHandoffTemplate tm) (tickInitializedWindowTemplate tm)

theorem tickResourceInverseSetupTemplate_embeds (tm : Turing.FinTM2) :
    (tickResourceInverseSetupTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickMetadataHandoffTemplate_embeds tm)
    (tickInitializedWindowTemplate_embeds tm)

theorem tickResourceInverseSetupTemplate_run (tm : Turing.FinTM2) :
    (tickResourceInverseSetupTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (tickMetadataHandoffTemplate_embeds tm)
    (tickMetadataHandoffTemplate_run tm) (tickInitializedWindowTemplate_run tm)

/-- Both setup components are silent and establish the exact initialized inverse register state. -/
theorem tickResourceInverseSetupTemplate_result (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickResourceInverseSetupTemplate tm).bytes cs=[] ∧
      (tickResourceInverseSetupTemplate tm).counters cs=tickResourceInverseStart tm cs := by
  constructor <;> rfl

/-- Actual prelude output supplies setup readiness and an actual polynomial instruction bound. -/
theorem tickResourceInverseSetupTemplate_polynomial (tm : Turing.FinTM2) (time : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      (∀ r,cs (workspaceTickRegister tm r)=operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r) →
      (∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → cs q=0) →
      (tickResourceInverseSetupTemplate tm).ready cs ∧
        (tickResourceInverseSetupTemplate tm).steps cs ≤ clock.eval n := by
  obtain ⟨ch,hh⟩ := tickResourceHandoff_polynomial_run tm time
  obtain ⟨cw,hw⟩ := tickInitializedWindowTemplate_polynomial tm (resourceCounterBudgetPolynomial tm time)
  refine ⟨ch+cw,?_⟩
  intro n cs hpull houtside
  have hs := (tickResourcePrelude_metadata tm n (time.eval n) cs hpull).2.2.2.2.1
  have handready := (tickMetadataHandoffTemplate_ready tm cs).2 hs
  have handfixed := (tickResourcePrelude_handoff_result tm n (time.eval n) cs hpull).1
  have windowready := (tickInitializedWindowTemplate_ready tm _).2 handfixed.2.2.1
  have hhand := (hh n cs hpull houtside Unit (fun _ => .halt) () []).2
  have hwindow := hw n ((tickMetadataHandoffTemplate tm).counters cs)
    (tickResourceHandoff_uniform_bound tm time n cs hpull houtside) windowready
  refine ⟨⟨handready,windowready⟩,?_⟩
  simpa only [tickResourceInverseSetupTemplate,sequenceProgramTemplate,Polynomial.eval_add] using
    Nat.add_le_add hhand hwindow

end ShiReversibleGenerator
