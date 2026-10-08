import ReversibleOutputCopyResourceCircuitCertificate
import ReversibleTickResourcePreludeExit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def outputCopyResourceCode (tm : Turing.FinTM2) (c d : Nat) := by
  classical
  exact chainedCounterCode (outputCopyResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
    (outputCopyMasterTemplate.code (fun _ : Unit => .halt) ())
    (tickResourcePreludeExit tm c d) (outputCopyMasterTemplate.entry ()) (.inl 0)

theorem outputCopyResourceCode_finite (tm : Turing.FinTM2) (c d : Nat) :
    Nonempty (Fintype (ResourcePreludeLabels tm c d Unit ⊕ outputCopyMasterTemplate.Labels Unit)) := by
  classical
  letI := outputCopyMasterTemplate.finite Unit inferInstance
  exact ⟨inferInstance⟩

theorem outputCopyResourcePreludeExit_halt (tm : Turing.FinTM2) (c d : Nat) :
    outputCopyResourcePreludeCode tm c d (fun _ : Unit => .halt) ()
      (tickResourcePreludeExit tm c d)=.halt := by
  unfold outputCopyResourcePreludeCode tickResourcePreludeExit resourcePreludeCode
  rw [initializedBudgetCode_embed,operationCode_embed,operationCode_embed]
  rfl

/-- The prelude, bridge and copy generator form one counted finite-control run. -/
theorem outputCopyResourceCode_joined_run (tm : Turing.FinTM2) (c d n : Nat) (ys payload : List Bool)
    (cs : OutputCopyMasterRegister → Nat) (first : Nat)
    (hfirst : CounterRun (outputCopyResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      ⟨some (.inl ()),outputCopyResourceInitial n,ys⟩ first
      ⟨some (tickResourcePreludeExit tm c d),cs,ys⟩)
    (hsecond : CounterRun (outputCopyMasterTemplate.code (fun _ : Unit => .halt) ())
      ⟨some (outputCopyMasterTemplate.entry ()),cs,ys⟩ (outputCopyMasterTemplate.steps cs)
      ⟨some (outputCopyMasterTemplate.exit ()),outputCopyMasterTemplate.counters cs,payload++ys⟩) :
    CounterRun (outputCopyResourceCode tm c d)
      ⟨some (.inl (.inl ())),outputCopyResourceInitial n,ys⟩
      (first+1+outputCopyMasterTemplate.steps cs)
      ⟨some (.inr (outputCopyMasterTemplate.exit ())),outputCopyMasterTemplate.counters cs,payload++ys⟩ := by
  classical
  simpa only [outputCopyResourceCode,CounterCfg.relabel,Option.map_some] using
    chainedCounterCode_run (outputCopyResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      (outputCopyMasterTemplate.code (fun _ : Unit => .halt) ())
      (tickResourcePreludeExit tm c d) (outputCopyMasterTemplate.entry ()) (.inl 0)
      (outputCopyResourcePreludeExit_halt tm c d) _ cs ys _ first _ hfirst hsecond

end ShiReversibleGenerator
