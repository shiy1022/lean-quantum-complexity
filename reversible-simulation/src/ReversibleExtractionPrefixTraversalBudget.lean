import ReversibleExtractionPrefixLoopBudgetStep
import ReversibleExtractionForwardPrefixLoop

set_option autoImplicit false
namespace ShiReversibleGenerator

structure ExtractionPrefixTraversalBudget (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTraversalRegister → Nat) : Prop where
  inner : ExtractionPrefixLoopBudget tm e B M spent (fun r => cs (extractionTermToTraversalRegister r))
  remaining : cs 22 ≤ B
  extra : cs 23 ≤ M

theorem extractionTraversal_pull_update22 (cs : ExtractionTraversalRegister → Nat) (k : Nat) :
    (fun r => Function.update cs (22 : ExtractionTraversalRegister) k (extractionTermToTraversalRegister r))=
      (fun r => cs (extractionTermToTraversalRegister r)) := by
  funext r
  apply Function.update_of_ne
  intro h
  have hv := congrArg Fin.val h
  have hr := r.isLt
  simp only [extractionTermToTraversalRegister] at hv
  omega

theorem extractionPrefixTraversalBudget_initial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M : Nat) (cs : ExtractionTraversalRegister → Nat) (hb : ∀ q,cs q ≤ B) (hm : B ≤ M) :
    ExtractionPrefixTraversalBudget tm e B M 0 cs := by
  exact ⟨extractionPrefixLoopBudget_initial tm e B M _ (fun r => hb _) hm,hb 22,(hb 23).trans hm⟩

theorem extractionPrefixTraversalBudget_update (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent k : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionPrefixTraversalBudget tm e B M spent cs) (hk : k ≤ B) :
    ExtractionPrefixTraversalBudget tm e B M spent (Function.update cs (22 : ExtractionTraversalRegister) k) := by
  refine ⟨?_,by simpa using hk,by simpa using h.extra⟩
  rw [extractionTraversal_pull_update22]
  exact h.inner

theorem extractionPrefixTraversalBudget_step (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride B M spent : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionPrefixTraversalBudget tm e B M spent cs)
    (hsmall : 2*B+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7) ≤ M)
    (hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
      (extractionForwardPrefixStepTemplate tm e stride).counters
        (fun r => cs (extractionTermToTraversalRegister r)) q ≤ M)
    (ha : ∀ q ∈ ([19,20,21] : List ExtractionTermRegister),
      (extractionForwardPrefixStepTemplate tm e stride).counters
        (fun r => cs (extractionTermToTraversalRegister r)) q ≤ M) :
    ExtractionPrefixTraversalBudget tm e B M (spent+1)
      ((extractionForwardPrefixTraversalStepTemplate tm e stride).counters cs) := by
  refine ⟨?_,?_,?_⟩
  · have hp := extractionPrefixLoopBudget_step tm e stride B M spent _ h.inner hsmall hf ha
    have he : (fun r => (extractionForwardPrefixTraversalStepTemplate tm e stride).counters cs
        (extractionTermToTraversalRegister r))=
      (extractionForwardPrefixStepTemplate tm e stride).counters
        (fun r => cs (extractionTermToTraversalRegister r)) := by
      funext r
      exact extractionTraversalLift_pull (extractionForwardPrefixStepTemplate tm e stride) cs r
    rw [he]
    exact hp
  · exact (extractionTraversalLift_outside (extractionForwardPrefixStepTemplate tm e stride) cs 22 (by decide)).trans_le h.remaining
  · exact (extractionTraversalLift_outside (extractionForwardPrefixStepTemplate tm e stride) cs 23 (by decide)).trans_le h.extra

theorem extractionPrefixTraversalBudget_uniform (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionPrefixTraversalBudget tm e B M spent cs) :
    ∀ q,cs q ≤ M+B+(37*extractionTermSchemaBudget tm e+2)*spent := by
  intro q
  by_cases hq : q.val < 22
  · let r : ExtractionTermRegister := ⟨q.val,hq⟩
    have he : extractionTermToTraversalRegister r=q := Fin.ext rfl
    have hi := extractionPrefixLoopBudget_uniform tm e B M spent _ h.inner r
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
