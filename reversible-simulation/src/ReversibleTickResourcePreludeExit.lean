import ReversibleTickResourcePreludeRun
import ReversibleCounterChain

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickResourcePreludeExit (tm : Turing.FinTM2) (c d : Nat) :
    ResourcePreludeLabels tm c d Unit :=
  initializedBudgetEmbed (operationExit (resourceLayoutOperations tm)
    (operationExit (workspaceOperations tm) ()))

theorem tickResourcePreludeExit_halt (tm : Turing.FinTM2) (c d : Nat) :
    tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ()
      (tickResourcePreludeExit tm c d)=.halt := by
  unfold tickResourcePreludeCode tickResourcePreludeExit resourcePreludeCode
  rw [initializedBudgetCode_embed,operationCode_embed,operationCode_embed]
  rfl

/-- The actual prefix endpoint retains its counters and output at the designated finite halt label. -/
theorem tickResourcePrelude_endpoint (tm : Turing.FinTM2) (c d : Nat)
    (final : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) (ResourcePreludeLabels tm c d Unit))
    (n : Nat) (ys : List Bool)
    (hpull : final.pullRegisters (workspaceTickRegister tm)=
      ⟨some (tickResourcePreludeExit tm c d),
        operationResult (workspaceOperations tm) (workspaceInitial tm n ((n+c)^d)),ys⟩) :
    final=⟨some (tickResourcePreludeExit tm c d),final.counters,ys⟩ := by
  apply CounterCfg.ext
  · simpa only [CounterCfg.pullRegisters] using congrArg (fun s => s.pc) hpull
  · rfl
  · simpa only [CounterCfg.pullRegisters] using congrArg (fun s => s.output) hpull

end ShiReversibleGenerator
