import ReversibleExtractionResourceQuantumPayload
import ReversibleRawPrinterProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Package the actual finite extraction program for composable raw-length phases, with no assumed generator. -/
theorem extractionRawPrinterTemplate_exists (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    ∃ p : CounterProgramTemplate ExtractionMasterRegister,
      p.Embeds ∧ p.Runs ∧
      (∀ cs,p.ready cs ↔ cs=extractionResourceInitial (cs (.inl 0))) ∧
      (∀ cs,p.bytes cs=extractionResourcePayload tm e backward (cs (.inl 0)) ((cs (.inl 0)+c)^d)) ∧
      (∀ cs,p.counters cs (.inr 16)=
        ((extractionForest tm e (cs (.inl 0)+(cs (.inl 0)+c)^d*machinePushBound tm+1)).map
          (fun p => formulaElementaryLayers p+1)).sum) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  classical
  obtain ⟨budget,clock,h⟩ := extractionResourceCode_polynomial_run tm e backward c d
  dsimp only at h
  have hs := fun n => h n []
  choose count hrun hclock hcount hbudget using hs
  letI := Classical.choice (extractionResourceCode_finite tm e backward c d)
  let p := rawPrinterProgramTemplate (extractionResourceCode tm e backward c d)
    (.inl (.inl ())) (.inr ((extractionResourceTemplate tm e backward).exit ())) (.inl 0)
    extractionResourceInitial
    (fun n => (extractionResourceTemplate tm e backward).counters (extractionResourceState tm n ((n+c)^d)))
    count (fun n => extractionResourcePayload tm e backward n ((n+c)^d))
  have hr : ∀ n,CounterRun (extractionResourceCode tm e backward c d)
      ⟨some (.inl (.inl ())),extractionResourceInitial n,[]⟩ (count n)
      ⟨some (.inr ((extractionResourceTemplate tm e backward).exit ())),
        (extractionResourceTemplate tm e backward).counters (extractionResourceState tm n ((n+c)^d)),
        extractionResourcePayload tm e backward n ((n+c)^d)⟩ := by
    intro n
    simpa only [List.append_nil] using hrun n
  have hhalt : extractionResourceCode tm e backward c d
      (.inr ((extractionResourceTemplate tm e backward).exit ()))=.halt := by
    change (((extractionResourceTemplate tm e backward).code (fun _ : Unit => .halt) ()
      ((extractionResourceTemplate tm e backward).exit ())).relabel Sum.inr)=.halt
    rw [extractionResourceTemplate_embeds tm e backward Unit (fun _ => .halt) () ()]
    rfl
  have hi : ∀ n q,extractionResourceInitial n q ≤ n := by
    intro n q
    cases q with
    | inl r =>
      simp only [extractionResourceInitial,resourceBudgetState]
      split_ifs <;> omega
    | inr r => exact Nat.zero_le _
  refine ⟨p,rawPrinterProgramTemplate_embeds _ _ _ _ _ _ _ _,
    rawPrinterProgramTemplate_run _ _ _ _ _ _ _ _ hhalt hr,?_,?_,?_,?_⟩
  · intro cs; rfl
  · intro cs; rfl
  · intro cs; exact hcount (cs (.inl 0))
  · intro bound
    exact ⟨rawPrinterProgramTemplate_budget _ _ _ _ _ _ _ _ clock bound hclock hi hr,
      rawPrinterProgramTemplate_polynomial _ _ _ _ _ _ _ _ clock bound hclock⟩

end ShiReversibleGenerator
