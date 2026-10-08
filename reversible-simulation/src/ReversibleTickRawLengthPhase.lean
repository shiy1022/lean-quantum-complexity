import ReversibleTickRawForwardPrinterTemplate
import ReversibleTickRawInversePrinterTemplate
import ReversibleRawLengthPhaseTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

noncomputable def tickResourcePayload (tm : Turing.FinTM2) (backward : Bool) (time : Polynomial Nat) (n : Nat) : List Bool :=
  if backward then tickResourceInversePayload tm time n else tickResourceForwardPayload tm time n

theorem tickRawPrinterTemplate_exists (tm : Turing.FinTM2) (backward : Bool) (c d : Nat) (hc : 0 < c) :
    ∃ p : CounterProgramTemplate (FixedLeafRegister (tickTraversalSupply tm)),
      p.Embeds ∧ p.Runs ∧
      (∀ cs,p.ready cs ↔ cs=tickResourceInitial tm (cs (.inl 0))) ∧
      (∀ cs,p.bytes cs=tickResourcePayload tm backward ((Polynomial.X+Polynomial.C c)^d) (cs (.inl 0))) ∧
      (∀ cs,p.counters cs (.inl 9)=(cs (.inl 0)+c)^d*
        tickForestLayerCount tm (cs (.inl 0)+(cs (.inl 0)+c)^d*machinePushBound tm+1)) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  cases backward
  · simpa only [tickResourcePayload,Bool.false_eq_true,if_false] using tickRawForwardPrinterTemplate_exists tm c d hc
  · simpa only [tickResourcePayload,if_true] using tickRawInversePrinterTemplate_exists tm c d hc

theorem tickResourceInitial_canonical (tm : Turing.FinTM2) (n : Nat) :
    tickResourceInitial tm n=Function.update (fun _ : FixedLeafRegister (tickTraversalSupply tm) => 0) (.inl 0) n := by
  funext q
  simp [tickResourceInitial,Function.update_apply]

/-- Both original history directions are actual finite phases with preserved length, exact total count and zero private workspace. -/
theorem tickRawLengthPhase_exists (tm : Turing.FinTM2) (backward : Bool) (c d : Nat) (hc : 0 < c) :
    ∃ q : CounterProgramTemplate (RawLengthPhaseRegister (FixedLeafRegister (tickTraversalSupply tm))),
      q.Embeds ∧ q.Runs ∧
      (∀ cs,cs (.inl 2)=0 → q.ready cs) ∧
      (∀ cs,q.bytes cs=tickResourcePayload tm backward ((Polynomial.X+Polynomial.C c)^d) (cs (.inl 0))) ∧
      (∀ cs,q.counters cs (.inl 1)=cs (.inl 1)+(cs (.inl 0)+c)^d*
        tickForestLayerCount tm (cs (.inl 0)+(cs (.inl 0)+c)^d*machinePushBound tm+1)) ∧
      (∀ cs,q.counters cs (.inl 0)=cs (.inl 0)) ∧
      (∀ cs,q.counters cs (.inl 2)=cs (.inl 2)) ∧
      (∀ cs r,q.counters cs (.inr r)=0) ∧
      (∀ bound : Polynomial Nat,q.CounterBound bound ∧ q.PolynomiallyTimed bound) := by
  obtain ⟨p,he,hr,hready,hbytes,hcount,hresources⟩ := tickRawPrinterTemplate_exists tm backward c d hc
  let q := rawLengthPhaseTemplate p (.inl 0) (.inl 9)
  refine ⟨q,rawLengthPhaseTemplate_embeds _ _ _,rawLengthPhaseTemplate_run _ _ _ he hr,?_,?_,?_,?_,?_,?_,?_⟩
  · intro cs hs
    apply rawLengthPhaseTemplate_ready _ _ _ _ cs hs
    intro n
    apply (hready _).2
    rw [Function.update_self]
    exact (tickResourceInitial_canonical tm n).symm
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
