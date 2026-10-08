import ReversibleTickResourcePureForwardRun
import ReversibleRawPrinterProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- A positive shifted-power budget packages the actual forward history printer at every input length. -/
theorem tickRawForwardPrinterTemplate_exists (tm : Turing.FinTM2) (c d : Nat) (hc : 0 < c) :
    ∃ p : CounterProgramTemplate (FixedLeafRegister (tickTraversalSupply tm)),
      p.Embeds ∧ p.Runs ∧
      (∀ cs,p.ready cs ↔ cs=tickResourceInitial tm (cs (.inl 0))) ∧
      (∀ cs,p.bytes cs=tickResourceForwardPayload tm ((Polynomial.X+Polynomial.C c)^d) (cs (.inl 0))) ∧
      (∀ cs,p.counters cs (.inl 9)=(cs (.inl 0)+c)^d*
        tickForestLayerCount tm (cs (.inl 0)+(cs (.inl 0)+c)^d*machinePushBound tm+1)) ∧
      (∀ bound : Polynomial Nat,p.CounterBound bound ∧ p.PolynomiallyTimed bound) := by
  classical
  obtain ⟨clock,h⟩ := tickResourcePureForwardCode_polynomial_run tm c d
  have hs := fun n => h n (Nat.pow_pos (by omega : 0 < n+c))
  dsimp only at hs
  choose count hrun hclock hcount using hs
  letI := Classical.choice (tickResourceForwardCode_finite tm c d)
  let p := rawPrinterProgramTemplate (tickResourceForwardCode tm c d)
    (.inl (.inl ())) (.inr ((tickHandoffForwardTemplate tm).exit ())) (.inl 0)
    (tickResourceInitial tm)
    (fun n => (tickHandoffForwardTemplate tm).counters (tickResourceState tm n ((n+c)^d)))
    count (fun n => tickResourceForwardPayload tm ((Polynomial.X+Polynomial.C c)^d) n)
  have hhalt : tickResourceForwardCode tm c d (.inr ((tickHandoffForwardTemplate tm).exit ()))=.halt := by
    change (((tickHandoffForwardTemplate tm).code (fun _ : Unit => .halt) ()
      ((tickHandoffForwardTemplate tm).exit ())).relabel Sum.inr)=.halt
    rw [tickHandoffForwardTemplate_embeds tm Unit (fun _ => .halt) () ()]
    rfl
  have hi : ∀ n q,tickResourceInitial tm n q ≤ n := by
    intro n q
    simp only [tickResourceInitial]
    split_ifs <;> omega
  refine ⟨p,rawPrinterProgramTemplate_embeds _ _ _ _ _ _ _ _,
    rawPrinterProgramTemplate_run _ _ _ _ _ _ _ _ hhalt hrun,?_,?_,?_,?_⟩
  · intro cs; rfl
  · intro cs; rfl
  · intro cs; exact hcount (cs (.inl 0))
  · intro bound
    exact ⟨rawPrinterProgramTemplate_budget _ _ _ _ _ _ _ _ clock bound hclock hi hrun,
      rawPrinterProgramTemplate_polynomial _ _ _ _ _ _ _ _ clock bound hclock⟩

end ShiReversibleGenerator
