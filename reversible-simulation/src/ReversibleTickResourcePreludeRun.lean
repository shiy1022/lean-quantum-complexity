import ReversibleTickWorkspaceRegisterInjection

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickResourcePreludeCode {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr WorkspaceRegister L) (stop : L) :=
  fun l => (resourcePreludeCode tm c d caller stop l).mapRegisters (workspaceTickRegister tm)

/-- Run the actual prelude in the history emitter's register file with its unchanged instruction clock. -/
theorem tickResourcePreludeCode_run {L : Type} (tm : Turing.FinTM2) (c d : Nat)
    (caller : L → CounterInstr WorkspaceRegister L) (stop : L) (n : Nat) (ys : List Bool) :
    ∃ final : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) (ResourcePreludeLabels tm c d L),
      CounterRun (tickResourcePreludeCode tm c d caller stop)
        ⟨some (.inl ()),tickResourceInitial tm n,ys⟩
        ((powerWork (n+c) d+2*d+2*c+1+
          operationSteps (resourceLayoutOperations tm) (resourceBudgetState n ((n+c)^d)))+
          operationSteps (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d))) final ∧
      final.pullRegisters (workspaceTickRegister tm)=
        ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm)
          (operationExit (workspaceOperations tm) stop))),
          operationResult (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d)),ys⟩ ∧
      ∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → final.counters q=0 := by
  let ambient : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) (ResourcePreludeLabels tm c d L) :=
    ⟨some (.inl ()),tickResourceInitial tm n,ys⟩
  have hs : ambient.pullRegisters (workspaceTickRegister tm)=
      ⟨some (.inl ()),resourceBudgetState n 0,ys⟩ := by
    apply CounterCfg.ext
    · rfl
    · exact tickResourceInitial_pull tm n
    · rfl
  obtain ⟨final,hfinal,hpull⟩ := CounterRun.mapRegisters (workspaceTickRegister tm) (workspaceTickRegister_injective tm)
    (resourcePreludeCode tm c d caller stop) (resourcePreludeCode_run tm c d caller stop n ys) ambient hs
  refine ⟨final,hfinal,hpull,?_⟩
  intro q hq
  have hf := CounterRun.mapRegisters_outside (workspaceTickRegister tm) (resourcePreludeCode tm c d caller stop) hfinal q hq
  have hzero : q ≠ .inl 0 := by
    intro h
    exact hq 0 ((workspaceTickRegister_zero tm).trans h.symm)
  simpa only [ambient,tickResourceInitial,if_neg hzero] using hf

/-- Polynomiality is inherited from the concrete counted prelude, without an encoding-size premise. -/
theorem tickResourcePreludeCode_polynomial (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat, ∀ (L : Type) (caller : L → CounterInstr WorkspaceRegister L) (stop : L) n ys,
      ∃ final : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) (ResourcePreludeLabels tm c d L),
        CounterRun (tickResourcePreludeCode tm c d caller stop)
          ⟨some (.inl ()),tickResourceInitial tm n,ys⟩ (clock.eval n) final ∧
        final.pullRegisters (workspaceTickRegister tm)=
          ⟨some (initializedBudgetEmbed (operationExit (resourceLayoutOperations tm)
            (operationExit (workspaceOperations tm) stop))),
            operationResult (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d)),ys⟩ ∧
        ∀ q,(∀ r,workspaceTickRegister tm r ≠ q) → final.counters q=0 := by
  obtain ⟨clock,hclock⟩ := resourcePreludeCode_clock_polynomial tm c d
  refine ⟨clock,?_⟩
  intro L caller stop n ys
  rw [←hclock n]
  exact tickResourcePreludeCode_run tm c d caller stop n ys

end ShiReversibleGenerator
