import ReversibleOutputCopyResourcePolynomialRun
import ReversibleRawPrinterProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Package the actual finite output-copy program for composable raw-length phases, with no assumed generator. -/
theorem outputCopyRawPrinterTemplate_exists (tm : Turing.FinTM2) (c d : Nat) :
    ∃ p : CounterProgramTemplate OutputCopyMasterRegister,
      p.Embeds ∧ p.Runs ∧
      (∀ cs,p.ready cs ↔ cs=outputCopyResourceInitial (cs (.inl 0))) ∧
      (∀ cs,p.bytes cs=outputCopyResourcePayload tm (cs (.inl 0)) ((cs (.inl 0)+c)^d)) ∧
      (∀ cs,p.counters cs (.inr 2)=2*(cs (.inl 0)+(cs (.inl 0)+c)^d*machinePushBound tm+1)+1) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  classical
  obtain ⟨clock,h⟩ := outputCopyResourceCode_polynomial_run tm c d
  dsimp only at h
  have hs := fun n => h n []
  choose count hrun hclock hcount hscratch using hs
  letI := Classical.choice (outputCopyResourceCode_finite tm c d)
  let p := rawPrinterProgramTemplate (outputCopyResourceCode tm c d)
    (.inl (.inl ())) (.inr (outputCopyMasterTemplate.exit ())) (.inl 0)
    outputCopyResourceInitial
    (fun n => outputCopyMasterTemplate.counters (outputCopyResourceState tm n ((n+c)^d)))
    count (fun n => outputCopyResourcePayload tm n ((n+c)^d))
  have hr : ∀ n,CounterRun (outputCopyResourceCode tm c d)
      ⟨some (.inl (.inl ())),outputCopyResourceInitial n,[]⟩ (count n)
      ⟨some (.inr (outputCopyMasterTemplate.exit ())),
        outputCopyMasterTemplate.counters (outputCopyResourceState tm n ((n+c)^d)),
        outputCopyResourcePayload tm n ((n+c)^d)⟩ := by
    intro n
    simpa only [List.append_nil] using hrun n
  have hhalt : outputCopyResourceCode tm c d
      (.inr (outputCopyMasterTemplate.exit ()))=.halt := by
    change ((outputCopyMasterTemplate.code (fun _ : Unit => .halt) ()
      (outputCopyMasterTemplate.exit ())).relabel Sum.inr)=.halt
    rw [outputCopyMasterTemplate_embeds Unit (fun _ => .halt) () ()]
    rfl
  have hi : ∀ n q,outputCopyResourceInitial n q ≤ n := by
    intro n q
    cases q with
    | inl r =>
      simp only [outputCopyResourceInitial,resourceBudgetState]
      split_ifs <;> omega
    | inr r => exact Nat.zero_le _
  refine ⟨p,rawPrinterProgramTemplate_embeds _ _ _ _ _ _ _ _,
    rawPrinterProgramTemplate_run _ _ _ _ _ _ _ _ hhalt hr,?_,?_,?_,?_⟩
  · intro cs; rfl
  · intro cs; rfl
  · intro cs
    exact (hcount (cs (.inl 0))).trans
      (outputCopyResource_metadata tm (cs (.inl 0)) ((cs (.inl 0)+c)^d)
        (outputCopyResourceState tm (cs (.inl 0)) ((cs (.inl 0)+c)^d)) (fun _ => rfl)).2.1
  · intro bound
    exact ⟨rawPrinterProgramTemplate_budget _ _ _ _ _ _ _ _ clock bound hclock hi hr,
      rawPrinterProgramTemplate_polynomial _ _ _ _ _ _ _ _ clock bound hclock⟩

end ShiReversibleGenerator
