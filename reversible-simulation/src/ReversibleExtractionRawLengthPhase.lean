import ReversibleExtractionRawPrinterTemplate
import ReversibleRawLengthPhaseTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionResourceInitial_canonical (n : Nat) :
    extractionResourceInitial n=Function.update (fun _ : ExtractionMasterRegister => 0) (.inl 0) n := by
  funext q
  cases q with
  | inl r => simp [extractionResourceInitial,resourceBudgetState,Function.update_apply]
  | inr r => simp [extractionResourceInitial,Function.update_apply]

/-- Both original extraction directions are actual finite phases preserving shared length, accumulating exact layers and clearing all private counters. -/
theorem extractionRawLengthPhase_exists (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (c d : Nat) :
    ∃ q : CounterProgramTemplate (RawLengthPhaseRegister ExtractionMasterRegister),
      q.Embeds ∧ q.Runs ∧
      (∀ cs,cs (.inl 2)=0 → q.ready cs) ∧
      (∀ cs,q.bytes cs=extractionResourcePayload tm e backward (cs (.inl 0)) ((cs (.inl 0)+c)^d)) ∧
      (∀ cs,q.counters cs (.inl 1)=cs (.inl 1)+
        ((extractionForest tm e (cs (.inl 0)+(cs (.inl 0)+c)^d*machinePushBound tm+1)).map
          (fun p => formulaElementaryLayers p+1)).sum) ∧
      (∀ cs,q.counters cs (.inl 0)=cs (.inl 0)) ∧
      (∀ cs,q.counters cs (.inl 2)=cs (.inl 2)) ∧
      (∀ cs r,q.counters cs (.inr r)=0) ∧
      (∀ bound : Polynomial Nat,q.CounterBound bound ∧ q.PolynomiallyTimed bound) := by
  obtain ⟨p,he,hr,hready,hbytes,hcount,hresources⟩ := extractionRawPrinterTemplate_exists tm e backward c d
  let q := rawLengthPhaseTemplate p (.inl 0) (.inr 16)
  refine ⟨q,rawLengthPhaseTemplate_embeds _ _ _,rawLengthPhaseTemplate_run _ _ _ he hr,?_,?_,?_,?_,?_,?_,?_⟩
  · intro cs hs
    apply rawLengthPhaseTemplate_ready _ _ _ _ cs hs
    intro n
    apply (hready _).2
    rw [Function.update_self]
    exact (extractionResourceInitial_canonical n).symm
  · intro cs
    rw [rawLengthPhaseTemplate_bytes,hbytes,Function.update_self]
  · intro cs
    rw [rawLengthPhaseTemplate_count,hcount,Function.update_self]
  · intro cs
    exact rawLengthPhaseTemplate_shared _ _ _ cs 0 (by decide)
  · intro cs
    exact rawLengthPhaseTemplate_shared _ _ _ cs 2 (by decide)
  · intro cs r
    exact rawLengthPhaseTemplate_cleared _ _ _ cs r
  · intro bound
    exact rawLengthPhaseTemplate_resources _ _ _ bound (hresources bound).1 (hresources bound).2

end ShiReversibleGenerator
