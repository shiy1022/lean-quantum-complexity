import ReversibleTickHandoffForwardTemplate
import ReversibleTickResourcePreludeExit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickResourceForwardCode (tm : Turing.FinTM2) (c d : Nat) := by
  classical
  exact chainedCounterCode (tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
    ((tickHandoffForwardTemplate tm).code (fun _ : Unit => .halt) ())
    (tickResourcePreludeExit tm c d) ((tickHandoffForwardTemplate tm).entry ()) (.inl 0)

/-- The entire resource setup, metadata handoff, and forward history printer is one finite control graph. -/
theorem tickResourceForwardCode_finite (tm : Turing.FinTM2) (c d : Nat) :
    Nonempty (Fintype (ResourcePreludeLabels tm c d Unit ⊕ (tickHandoffForwardTemplate tm).Labels Unit)) := by
  classical
  letI := (tickHandoffForwardTemplate tm).finite Unit inferInstance
  exact ⟨inferInstance⟩

/-- Count the real resource prefix, the connecting branch, and the complete printer run. -/
theorem tickResourceForwardCode_joined_run (tm : Turing.FinTM2) (c d n : Nat) (ys payload : List Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (first : Nat)
    (hfirst : CounterRun (tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      ⟨some (.inl ()),tickResourceInitial tm n,ys⟩ first
      ⟨some (tickResourcePreludeExit tm c d),cs,ys⟩)
    (hsecond : CounterRun ((tickHandoffForwardTemplate tm).code (fun _ : Unit => .halt) ())
      ⟨some ((tickHandoffForwardTemplate tm).entry ()),cs,ys⟩
      ((tickHandoffForwardTemplate tm).steps cs)
      ⟨some ((tickHandoffForwardTemplate tm).exit ()),
        (tickHandoffForwardTemplate tm).counters cs,payload++ys⟩) :
    CounterRun (tickResourceForwardCode tm c d)
      ⟨some (.inl (.inl ())),tickResourceInitial tm n,ys⟩
      (first+1+(tickHandoffForwardTemplate tm).steps cs)
      ⟨some (.inr ((tickHandoffForwardTemplate tm).exit ())),
        (tickHandoffForwardTemplate tm).counters cs,payload++ys⟩ := by
  classical
  simpa only [tickResourceForwardCode,CounterCfg.relabel,Option.map_some] using
    chainedCounterCode_run (tickResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      ((tickHandoffForwardTemplate tm).code (fun _ : Unit => .halt) ())
      (tickResourcePreludeExit tm c d) ((tickHandoffForwardTemplate tm).entry ()) (.inl 0)
      (tickResourcePreludeExit_halt tm c d) _ cs ys _ first _ hfirst hsecond

end ShiReversibleGenerator
