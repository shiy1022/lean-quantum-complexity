import ReversibleExtractionResourceCircuitCertificate
import ReversibleTickResourcePreludeExit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def extractionResourceCode (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool) (c d : Nat) := by
  classical
  exact chainedCounterCode (extractionResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
    ((extractionResourceTemplate tm e backward).code (fun _ : Unit => .halt) ())
    (tickResourcePreludeExit tm c d) ((extractionResourceTemplate tm e backward).entry ()) (.inl 0)

theorem extractionResourceCode_finite (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool) (c d : Nat) :
    Nonempty (Fintype (ResourcePreludeLabels tm c d Unit ⊕ (extractionResourceTemplate tm e backward).Labels Unit)) := by
  classical
  letI := (extractionResourceTemplate tm e backward).finite Unit inferInstance
  exact ⟨inferInstance⟩

theorem extractionResourcePreludeExit_halt (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool) (c d : Nat) :
    extractionResourcePreludeCode tm c d (fun _ : Unit => .halt) ()
      (tickResourcePreludeExit tm c d)=.halt := by
  unfold extractionResourcePreludeCode tickResourcePreludeExit resourcePreludeCode
  rw [initializedBudgetCode_embed,operationCode_embed,operationCode_embed]
  rfl

/-- The prelude, bridge and copy generator form one counted finite-control run. -/
theorem extractionResourceCode_joined_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool) (c d n : Nat) (ys payload : List Bool)
    (cs : ExtractionMasterRegister → Nat) (first : Nat)
    (hfirst : CounterRun (extractionResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      ⟨some (.inl ()),extractionResourceInitial n,ys⟩ first
      ⟨some (tickResourcePreludeExit tm c d),cs,ys⟩)
    (hsecond : CounterRun ((extractionResourceTemplate tm e backward).code (fun _ : Unit => .halt) ())
      ⟨some ((extractionResourceTemplate tm e backward).entry ()),cs,ys⟩ ((extractionResourceTemplate tm e backward).steps cs)
      ⟨some ((extractionResourceTemplate tm e backward).exit ()),(extractionResourceTemplate tm e backward).counters cs,payload++ys⟩) :
    CounterRun (extractionResourceCode tm e backward c d)
      ⟨some (.inl (.inl ())),extractionResourceInitial n,ys⟩
      (first+1+(extractionResourceTemplate tm e backward).steps cs)
      ⟨some (.inr ((extractionResourceTemplate tm e backward).exit ())),(extractionResourceTemplate tm e backward).counters cs,payload++ys⟩ := by
  classical
  simpa only [extractionResourceCode,CounterCfg.relabel,Option.map_some] using
    chainedCounterCode_run (extractionResourcePreludeCode tm c d (fun _ : Unit => .halt) ())
      ((extractionResourceTemplate tm e backward).code (fun _ : Unit => .halt) ())
      (tickResourcePreludeExit tm c d) ((extractionResourceTemplate tm e backward).entry ()) (.inl 0)
      (extractionResourcePreludeExit_halt tm e backward c d) _ cs ys _ first _ hfirst hsecond

end ShiReversibleGenerator
