import ReversibleInitializerResourceProgram
import ReversibleRawPrinterProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

noncomputable def initializerResourcePayload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (c d n : Nat) : List Bool :=
  ((initializationQuantumLayers tm e
    ((initializationCapacityPolynomial tm ((Polynomial.X+Polynomial.C c)^d)).eval n) n backward).map ShiBQP.encLayer).flatten

/-- The actual initializer's raw-length finite graph has a composable continuation and exact original layer count. -/
theorem initializerRawPrinterTemplate_exists (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    ∃ p : CounterProgramTemplate InitializationRegister,
      p.Embeds ∧ p.Runs ∧
      (∀ cs,p.ready cs ↔ cs=initializerResourceInitial (cs (.inl 0))) ∧
      (∀ cs,p.bytes cs=initializerResourcePayload tm e backward c d (cs (.inl 0))) ∧
      (∀ cs,p.counters cs (.inr 10)=initializationForestLayerCount tm e
        ((initializationCapacityPolynomial tm ((Polynomial.X+Polynomial.C c)^d)).eval (cs (.inl 0))) (cs (.inl 0))) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  classical
  obtain ⟨clock,h⟩ := initializerResourceCode_polynomial_run tm e backward c d
  dsimp only at h
  choose count hrun hclock hcount using h
  let time : Polynomial Nat := (Polynomial.X+Polynomial.C c)^d
  let final := fun n => initializerSequenceCounters (rankedInitializerComponents tm e backward) n
    (initializationPreludeCounters tm time n) []
  letI := Classical.choice (initializerResourceCode_finite tm e backward c d)
  let p := rawPrinterProgramTemplate (initializerResourceCode tm e backward c d)
    (.inl (.inl ())) (.inr (initializerSequenceExit (rankedInitializerComponents tm e backward))) (.inl 0)
    initializerResourceInitial final count (initializerResourcePayload tm e backward c d)
  have hr : ∀ n,CounterRun (initializerResourceCode tm e backward c d)
      ⟨some (.inl (.inl ())),initializerResourceInitial n,[]⟩ (count n)
      ⟨some (.inr (initializerSequenceExit (rankedInitializerComponents tm e backward))),final n,
        initializerResourcePayload tm e backward c d n⟩ := hrun
  have hhalt : initializerResourceCode tm e backward c d
      (.inr (initializerSequenceExit (rankedInitializerComponents tm e backward)))=.halt := by
    change ((rankedInitializerCode tm e backward
      (initializerSequenceExit (rankedInitializerComponents tm e backward))).relabel Sum.inr)=.halt
    rw [rankedInitializer_exit]
    rfl
  have hi : ∀ n q,initializerResourceInitial n q ≤ n := by
    intro n q
    cases q with
    | inl r =>
      simp only [initializerResourceInitial,Sum.elim_inl,resourceBudgetState]
      split_ifs <;> omega
    | inr r => exact Nat.zero_le _
  refine ⟨p,rawPrinterProgramTemplate_embeds _ _ _ _ _ _ _ _,
    rawPrinterProgramTemplate_run _ _ _ _ _ _ _ _ hhalt hr,?_,?_,?_,?_⟩
  · intro cs; rfl
  · intro cs; rfl
  · intro cs
    exact (hcount (cs (.inl 0))).trans (initializationQuantumLayers_length tm e _ _ backward)
  · intro bound
    exact ⟨rawPrinterProgramTemplate_budget _ _ _ _ _ _ _ _ clock bound hclock hi hr,
      rawPrinterProgramTemplate_polynomial _ _ _ _ _ _ _ _ clock bound hclock⟩

end ShiReversibleGenerator
