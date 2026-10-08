import ReversibleTickResourceForwardPolynomialRun
import ReversibleTickResourceInverseProgram
import ReversibleTemplateRegisterInjectionData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

noncomputable def tickResourceState (tm : Turing.FinTM2) (n budget : Nat) :
    FixedLeafRegister (tickTraversalSupply tm) → Nat :=
  injectedTemplateCounters (workspaceTickRegister tm) (fun _ => 0)
    (operationResult (workspaceOperations tm) (workspaceInitial tm n budget))

theorem tickResourceState_pull (tm : Turing.FinTM2) (n budget : Nat) (r : WorkspaceRegister) :
    tickResourceState tm n budget (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r :=
  injectedTemplateCounters_pull _ (workspaceTickRegister_injective tm) _ _ _

theorem tickResourceState_outside (tm : Turing.FinTM2) (n budget : Nat)
    (q : FixedLeafRegister (tickTraversalSupply tm)) (hq : ∀ r,workspaceTickRegister tm r ≠ q) :
    tickResourceState tm n budget q=0 := injectedTemplateCounters_outside _ _ _ _ hq

/-- The actual prelude ends in a pure metadata state, so history phases can be packaged independently of any printed suffix. -/
theorem tickResourcePreludeCode_pure_run (tm : Turing.FinTM2) (c d : Nat) :
    ∃ clock : Polynomial Nat,∀ n (ys : List Bool),
      CounterRun (tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
        ⟨some (.inl ()),tickResourceInitial tm n,ys⟩ (clock.eval n)
        ⟨some (tickResourcePreludeExit tm c d),tickResourceState tm n ((n+c)^d),ys⟩ := by
  obtain ⟨clock,hclock⟩ := tickResourcePreludeCode_polynomial tm c d
  refine ⟨clock,?_⟩
  intro n ys
  obtain ⟨final,hr,hpull,houtside⟩ := hclock Unit (fun _ => .halt) () n ys
  have hc : final.counters=tickResourceState tm n ((n+c)^d) := by
    apply injectedTemplateCounters_unique
    · intro r
      exact congrArg (fun s => s.counters r) hpull
    · intro q hq
      exact houtside q hq
  have he : final=⟨some (tickResourcePreludeExit tm c d),tickResourceState tm n ((n+c)^d),ys⟩ := by
    apply CounterCfg.ext
    · simpa only [CounterCfg.pullRegisters,tickResourcePreludeExit] using congrArg (fun s => s.pc) hpull
    · exact hc
    · simpa only [CounterCfg.pullRegisters] using congrArg (fun s => s.output) hpull
  rw [he] at hr
  exact hr

end ShiReversibleGenerator
