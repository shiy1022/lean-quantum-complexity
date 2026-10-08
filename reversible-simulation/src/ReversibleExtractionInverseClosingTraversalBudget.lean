import ReversibleExtractionInverseClosingBudget
import ReversibleExtractionPrefixTraversalBudget
import ReversibleExtractionInverseClosingLoop

set_option autoImplicit false
namespace ShiReversibleGenerator

structure ExtractionInverseClosingTraversalBudget (tm : Turing.FinTM2) 
    (B M spent : Nat) (cs : ExtractionTraversalRegister → Nat) : Prop where
  inner : ExtractionInverseClosingBudget tm B M spent (fun r => cs (extractionTermToTraversalRegister r))
  remaining : cs 22 ≤ B
  extra : cs 23 ≤ M

theorem extractionInverseClosingTraversalBudget_initial (tm : Turing.FinTM2) 
    (B M : Nat) (cs : ExtractionTraversalRegister → Nat) (hb : ∀ q,cs q ≤ B) (hm : B ≤ M) :
    ExtractionInverseClosingTraversalBudget tm B M 0 cs := by
  exact ⟨extractionInverseClosingBudget_initial tm B M _ (fun r => hb _) hm,hb 22,(hb 23).trans hm⟩

theorem extractionInverseClosingTraversalBudget_update (tm : Turing.FinTM2) 
    (B M spent k : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionInverseClosingTraversalBudget tm B M spent cs) (hk : k ≤ B) :
    ExtractionInverseClosingTraversalBudget tm B M spent (Function.update cs (22 : ExtractionTraversalRegister) k) := by
  refine ⟨?_,by simpa using hk,by simpa using h.extra⟩
  rw [extractionTraversal_pull_update22]
  exact h.inner

theorem extractionInverseClosingTraversalBudget_step (tm : Turing.FinTM2) 
    (B M spent : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionInverseClosingTraversalBudget tm B M spent cs)
    (hs : spent ≤ B)
    (hsmall : 4*B+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7)+3 ≤ M) :
    ExtractionInverseClosingTraversalBudget tm B M (spent+1)
      ((extractionInverseClosingTraversalStepTemplate tm).counters cs) := by
  refine ⟨?_,?_,?_⟩
  · have hp := extractionInverseClosingBudget_step tm B M spent _ h.inner hs hsmall
    have he : (fun r => (extractionInverseClosingTraversalStepTemplate tm).counters cs
        (extractionTermToTraversalRegister r))=
      (extractionInverseClosingStepTemplate tm).counters
        (fun r => cs (extractionTermToTraversalRegister r)) := by
      funext r
      exact extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) cs r
    rw [he]
    exact hp
  · exact (extractionTraversalLift_outside (extractionInverseClosingStepTemplate tm) cs 22 (by decide)).trans_le h.remaining
  · exact (extractionTraversalLift_outside (extractionInverseClosingStepTemplate tm) cs 23 (by decide)).trans_le h.extra

theorem extractionInverseClosingTraversalBudget_uniform (tm : Turing.FinTM2) 
    (B M spent : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionInverseClosingTraversalBudget tm B M spent cs) :
    ∀ q,cs q ≤ M+B+41*spent := by
  intro q
  by_cases hq : q.val < 22
  · let r : ExtractionTermRegister := ⟨q.val,hq⟩
    have he : extractionTermToTraversalRegister r=q := Fin.ext rfl
    have hi := extractionInverseClosingBudget_uniform tm B M spent _ h.inner r
    simpa only [he] using hi
  · have hlt := q.isLt
    by_cases h22 : q.val=22
    · have he : q=(22 : ExtractionTraversalRegister) := Fin.ext h22
      subst q
      exact h.remaining.trans (by omega)
    · have he : q=(23 : ExtractionTraversalRegister) := Fin.ext (by omega)
      subst q
      exact h.extra.trans (by omega)

end ShiReversibleGenerator
