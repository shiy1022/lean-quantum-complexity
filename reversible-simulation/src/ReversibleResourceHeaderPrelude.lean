import ReversibleResourceRawPrinterTemplate
import ReversibleRawLengthPreparationTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem resourceBudgetState_canonical (n : Nat) :
    resourceBudgetState n 0=Function.update (fun _ : WorkspaceRegister => 0) 0 n := by
  funext r
  simp [resourceBudgetState,Function.update_apply]

/-- Header metadata is computed by the actual finite resource prelude, preserving the body's accumulated count. -/
theorem resourceHeaderPreludeTemplate_exists (tm : Turing.FinTM2) (c d : Nat) :
    ∃ q : CounterProgramTemplate (RawLengthPhaseRegister WorkspaceRegister),
      q.Embeds ∧ q.Runs ∧
      (∀ cs,cs (.inl 2)=0 → q.ready cs) ∧
      (∀ cs,q.bytes cs=[]) ∧
      (∀ cs r,q.counters cs (.inr r)=operationResult (workspaceOperations tm)
        (workspaceInitial tm (cs (.inl 0)) ((cs (.inl 0)+c)^d)) r) ∧
      (∀ cs j,q.counters cs (.inl j)=cs (.inl j)) ∧
      (∀ bound : Polynomial Nat,q.CounterBound bound ∧ q.PolynomiallyTimed bound) := by
  obtain ⟨p,he,hr,hready,hbytes,hc,hresources⟩ := resourceRawPrinterTemplate_exists tm c d
  let q := rawLengthPreparationTemplate p (0 : WorkspaceRegister)
  refine ⟨q,rawLengthPreparationTemplate_embeds _ _,rawLengthPreparationTemplate_run _ _ he hr,?_,?_,?_,?_,?_⟩
  · intro cs hs
    apply rawLengthPreparationTemplate_ready _ _ _ cs hs
    intro n
    apply (hready _).2
    rw [Function.update_self]
    exact (resourceBudgetState_canonical n).symm
  · intro cs
    rw [rawLengthPreparationTemplate_bytes,hbytes]
  · intro cs r
    rw [rawLengthPreparationTemplate_private,hc,Function.update_self]
  · intro cs j
    exact rawLengthPreparationTemplate_shared _ _ cs j
  · intro bound
    exact rawLengthPreparationTemplate_resources _ _ bound (hresources bound).1 (hresources bound).2

end ShiReversibleGenerator
