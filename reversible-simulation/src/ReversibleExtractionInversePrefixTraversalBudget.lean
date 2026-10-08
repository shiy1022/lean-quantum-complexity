import ReversibleExtractionInversePrefixBudgetStep
import ReversibleExtractionPrefixTraversalBudget
import ReversibleExtractionInversePrefixLoop

set_option autoImplicit false
namespace ShiReversibleGenerator

structure ExtractionInversePrefixTraversalBudget (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTraversalRegister → Nat) : Prop where
  inner : ExtractionInversePrefixBudget tm e B M spent (fun r => cs (extractionTermToTraversalRegister r))
  remaining : cs 22 ≤ B
  extra : cs 23 ≤ M

theorem extractionInversePrefixTraversalBudget_initial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M : Nat) (cs : ExtractionTraversalRegister → Nat) (hb : ∀ q,cs q ≤ B) (hm : B ≤ M) :
    ExtractionInversePrefixTraversalBudget tm e B M 0 cs := by
  exact ⟨extractionInversePrefixBudget_initial tm e B M _ (fun r => hb _) hm,hb 22,(hb 23).trans hm⟩

theorem extractionInversePrefixTraversalBudget_update (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent k : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionInversePrefixTraversalBudget tm e B M spent cs) (hk : k ≤ B) :
    ExtractionInversePrefixTraversalBudget tm e B M spent (Function.update cs (22 : ExtractionTraversalRegister) k) := by
  refine ⟨?_,by simpa using hk,by simpa using h.extra⟩
  rw [extractionTraversal_pull_update22]
  exact h.inner

theorem extractionInversePrefixTraversalBudget_step (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride B M spent : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionInversePrefixTraversalBudget tm e B M spent cs)
    (hs : spent ≤ B)
    (hsmall : 4*B+(1+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7))*B+
      (10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7)+1 ≤ M)
    (hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
      (extractionInversePrefixStepTemplate tm e stride).counters
        (fun r => cs (extractionTermToTraversalRegister r)) q ≤ M)
    (ha : (extractionInversePrefixStepTemplate tm e stride).counters
        (fun r => cs (extractionTermToTraversalRegister r)) 20 ≤ M) :
    ExtractionInversePrefixTraversalBudget tm e B M (spent+1)
      ((extractionInversePrefixTraversalStepTemplate tm e stride).counters cs) := by
  refine ⟨?_,?_,?_⟩
  · have hp := extractionInversePrefixBudget_step tm e stride B M spent _ h.inner hs hsmall hf ha
    have he : (fun r => (extractionInversePrefixTraversalStepTemplate tm e stride).counters cs
        (extractionTermToTraversalRegister r))=
      (extractionInversePrefixStepTemplate tm e stride).counters
        (fun r => cs (extractionTermToTraversalRegister r)) := by
      funext r
      exact extractionTraversalLift_pull (extractionInversePrefixStepTemplate tm e stride) cs r
    rw [he]
    exact hp
  · exact (extractionTraversalLift_outside (extractionInversePrefixStepTemplate tm e stride) cs 22 (by decide)).trans_le h.remaining
  · exact (extractionTraversalLift_outside (extractionInversePrefixStepTemplate tm e stride) cs 23 (by decide)).trans_le h.extra

theorem extractionInversePrefixTraversalBudget_uniform (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTraversalRegister → Nat)
    (h : ExtractionInversePrefixTraversalBudget tm e B M spent cs) :
    ∀ q,cs q ≤ M+B+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7+37*extractionTermSchemaBudget tm e+3)*spent := by
  intro q
  by_cases hq : q.val < 22
  · let r : ExtractionTermRegister := ⟨q.val,hq⟩
    have he : extractionTermToTraversalRegister r=q := Fin.ext rfl
    have hi := extractionInversePrefixBudget_uniform tm e B M spent _ h.inner r
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
