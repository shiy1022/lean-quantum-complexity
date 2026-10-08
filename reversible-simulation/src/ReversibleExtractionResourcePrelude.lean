import ReversibleExtractionResourceSetupResources
import ReversibleResourceCounterBounds

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def extractionResourceInitial (n : Nat) : ExtractionMasterRegister → Nat :=
  fun q => match q with
    | .inl r => resourceBudgetState n 0 r
    | .inr _ => 0

noncomputable def extractionResourcePreludeCode {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr WorkspaceRegister L) (stop : L) :=
  fun l => (resourcePreludeCode tm c d caller stop l).mapRegisters
    (Sum.inl : WorkspaceRegister → ExtractionMasterRegister)

/-- The resource prelude runs from raw input length in the copy generator's finite register file. -/
theorem extractionResourcePreludeCode_run {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr WorkspaceRegister L) (stop : L) (n : Nat) (ys : List Bool) :
    ∃ final : CounterCfg ExtractionMasterRegister (ResourcePreludeLabels tm c d L),
      CounterRun (extractionResourcePreludeCode tm c d caller stop)
        ⟨some (.inl ()),extractionResourceInitial n,ys⟩
        ((powerWork (n+c) d+2*d+2*c+1+
          operationSteps (resourceLayoutOperations tm) (resourceBudgetState n ((n+c)^d)))+
          operationSteps (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d))) final ∧
      final.pullRegisters Sum.inl=
        ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm)
          (operationExit (workspaceOperations tm) stop))),
          operationResult (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d)),ys⟩ ∧
      ∀ q : ExtractionForestRegister,final.counters (.inr q)=0 := by
  let ambient : CounterCfg ExtractionMasterRegister (ResourcePreludeLabels tm c d L) :=
    ⟨some (.inl ()),extractionResourceInitial n,ys⟩
  have hs : ambient.pullRegisters Sum.inl=
      ⟨some (.inl ()),resourceBudgetState n 0,ys⟩ := rfl
  obtain ⟨final,hfinal,hpull⟩ := CounterRun.mapRegisters
    (Sum.inl : WorkspaceRegister → ExtractionMasterRegister) (by intro a b h; cases h; rfl)
    (resourcePreludeCode tm c d caller stop) (resourcePreludeCode_run tm c d caller stop n ys) ambient hs
  refine ⟨final,hfinal,hpull,?_⟩
  intro q
  have hf := CounterRun.mapRegisters_outside
    (Sum.inl : WorkspaceRegister → ExtractionMasterRegister) (resourcePreludeCode tm c d caller stop)
    hfinal (.inr q) (by intro r; simp)
  exact hf

/-- All counters in the actual prelude endpoint obey the existing resource polynomial. -/
theorem extractionResourcePrelude_uniform_bound (tm : Turing.FinTM2) (time : Polynomial Nat) (n : Nat)
    (cs : ExtractionMasterRegister → Nat)
    (hpull : ∀ r,cs (.inl r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n (time.eval n)) r)
    (houtside : ∀ q : ExtractionForestRegister,cs (.inr q)=0) :
    ∀ q,cs q ≤ (resourceCounterBudgetPolynomial tm time).eval n := by
  intro q
  cases q with
  | inl r => rw [hpull]; exact resourceCounterBudgetPolynomial_bound tm time n r
  | inr r => rw [houtside]; exact Nat.zero_le _

/-- The actual prelude instruction count is a polynomial in the raw input length. -/
theorem extractionResourcePreludeCode_polynomial (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat, ∀ (L : Type) (caller : L → CounterInstr WorkspaceRegister L) (stop : L) n ys,
      ∃ final : CounterCfg ExtractionMasterRegister (ResourcePreludeLabels tm c d L),
        CounterRun (extractionResourcePreludeCode tm c d caller stop)
          ⟨some (.inl ()),extractionResourceInitial n,ys⟩ (clock.eval n) final ∧
        final.pullRegisters Sum.inl=
          ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm)
            (operationExit (workspaceOperations tm) stop))),
            operationResult (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d)),ys⟩ ∧
        ∀ q : ExtractionForestRegister,final.counters (.inr q)=0 := by
  obtain ⟨clock,hclock⟩ := resourcePreludeCode_clock_polynomial tm c d
  refine ⟨clock,?_⟩
  intro L caller stop n ys
  rw [←hclock n]
  exact extractionResourcePreludeCode_run tm c d caller stop n ys

end ShiReversibleGenerator
