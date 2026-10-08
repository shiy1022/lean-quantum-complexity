import ReversibleExtractionSizeMaster

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionSizeLoopTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeLoopTemplate tm).bytes cs=[] := by
  have h : ∀ k cs,descendingTemplateBytes (extractionSizeStepTemplate tm) 2 k cs=[] := by
    intro k
    induction k with
    | zero => intro cs; rfl
    | succ k ih => intro cs; simp [descendingTemplateBytes,ih,extractionSizeStepTemplate_bytes]
  exact h _ _

theorem extractionSizeMasterTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeMasterTemplate tm).bytes cs=[] := by
  change (extractionSizeLoopTemplate tm).bytes (extractionSizeSetupTemplate.counters cs) ++
    extractionSizeSetupTemplate.bytes cs=[]
  rw [extractionSizeLoopTemplate_bytes,extractionSizeSetupTemplate_bytes]
  rfl

/-- Actual finite-program execution computes the exact extraction formula size in polynomial time,
starting with arbitrary scratch counters and preserving the emitted circuit prefix. -/
theorem extractionSizeMasterTemplate_certificate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : ExtractionSizeRegister → Nat), (∀ q,cs q ≤ bound.eval n) →
      ∀ (L : Type) (caller : L → CounterInstr ExtractionSizeRegister L) (stop : L) (ys : List Bool),
      let p := extractionSizeMasterTemplate tm
      CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
        ⟨some (p.exit stop),p.counters cs,ys⟩ ∧ p.steps cs ≤ clock.eval n ∧
      p.counters cs 4=(extractionFormula tm e (cs 0) (cs 1)).size ∧ p.counters cs 2=0 := by
  obtain ⟨clock,hclock⟩ := extractionSizeMasterTemplate_polynomial tm bound
  refine ⟨clock,?_⟩
  intro n cs hb L caller stop ys
  dsimp only
  have hr := extractionSizeMasterTemplate_ready tm cs
  have hrun := extractionSizeMasterTemplate_run tm L caller stop cs ys hr
  rw [extractionSizeMasterTemplate_bytes,List.nil_append] at hrun
  exact ⟨hrun,hclock n cs hb hr,extractionSizeMasterTemplate_result tm e cs⟩

end ShiReversibleGenerator
