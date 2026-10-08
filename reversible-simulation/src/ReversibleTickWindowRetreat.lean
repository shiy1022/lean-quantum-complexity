import ReversibleCounterPairRetreat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Calculate the real padded slice width, then subtract it from both window pointers. -/
noncomputable def tickWindowRetreatTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  sequenceProgramTemplate
    (counterAffineCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 4) (.inl 5)
      (tickWidthOffset tm*(bound+1)) (tickWidthSlope tm*(bound+1)) 0)
    (counterPairRetreatTemplate (.inl 0) (tickTraversalSpare tm 2) (tickTraversalSpare tm 4))

theorem tickWindowRetreatTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickWindowRetreatTemplate tm bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
    (counterPairRetreatTemplate_embeds _ _ _)

theorem tickWindowRetreatTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickWindowRetreatTemplate tm bound).Runs := by
  apply sequenceProgramTemplate_run
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · apply counterAffineCopyProgramTemplate_run
    · simp [tickTraversalSpare]
    · simp [tickTraversalSpare]
    · simp [tickTraversalSpare]
  · exact counterPairRetreatTemplate_run _ _ _

theorem tickWindowRetreatTemplate_ready (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickWindowRetreatTemplate tm bound).ready cs ↔ cs (.inl 5)=0 := by
  change (cs (.inl 5)=0 ∧ _) ↔ _
  constructor
  · exact And.left
  · intro hs
    refine ⟨hs,counterPairRetreatTemplate_ready _ _ _ ?_ ?_ _⟩
    · simp [tickTraversalSpare]
    · exact fun h => (by decide : (2 : Fin 8) ≠ 4) (tickTraversalSpare_injective tm h)

theorem tickWindowRetreatTemplate_counters (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickWindowRetreatTemplate tm bound).counters cs=
      Function.update (Function.update (Function.update cs (.inl 0)
        (cs (.inl 0)-configurationWidth tm (cs (.inl 1))*(bound+1))) (tickTraversalSpare tm 2)
        (cs (tickTraversalSpare tm 2)-configurationWidth tm (cs (.inl 1))*(bound+1)))
        (tickTraversalSpare tm 4) 0 := by
  change (counterPairRetreatTemplate (.inl 0) (tickTraversalSpare tm 2) (tickTraversalSpare tm 4)).counters _=_
  rw [counterPairRetreatTemplate_counters _ _ _ (by simp [tickTraversalSpare])
    (by simp [tickTraversalSpare]) (fun h => (by decide : (2 : Fin 8) ≠ 4) (tickTraversalSpare_injective tm h))]
  have hw : tickWidthSlope tm*(bound+1)*cs (.inl 1)+tickWidthOffset tm*(bound+1)-0=
      configurationWidth tm (cs (.inl 1))*(bound+1) := by
    rw [tickWidth_affine]
    simp only [Nat.sub_zero]
    ring
  have h04 : (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 4 := by simp [tickTraversalSpare]
  have h24 : tickTraversalSpare tm 2 ≠ tickTraversalSpare tm 4 := fun h =>
    (by decide : (2 : Fin 8) ≠ 4) (tickTraversalSpare_injective tm h)
  simp only [counterAffineCopyProgramTemplate,hw,Function.update_self,
    Function.update_of_ne h04,Function.update_of_ne h24]
  funext q
  by_cases hq : q=tickTraversalSpare tm 4
  · subst q; simp
  · simp only [Function.update_apply,hq,ite_false]


theorem tickWindowRetreatTemplate_bytes (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickWindowRetreatTemplate tm bound).bytes cs=[] := by
  change (counterPairRetreatTemplate _ _ _).bytes _++[]=[]
  rw [counterPairRetreatTemplate_bytes]
  rfl

theorem tickWindowRetreatTemplate_polynomial (tm : Turing.FinTM2) (bound : Nat)
    (budget : Polynomial Nat) : (tickWindowRetreatTemplate tm bound).PolynomiallyTimed budget := by
  let coefficient := tickWidthSlope tm*(bound+1)
  let positive := tickWidthOffset tm*(bound+1)
  let nextBudget := budget+Polynomial.C coefficient*budget+Polynomial.C positive
  apply sequenceProgramTemplate_polynomial _ _ budget nextBudget
  · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ budget
  · intro n cs hb _ q
    change Function.update cs (tickTraversalSpare tm 4) (coefficient*cs (.inl 1)+positive-0) q ≤ nextBudget.eval n
    simp only [nextBudget,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Nat.sub_zero]
    by_cases hq : q=tickTraversalSpare tm 4
    · subst q
      rw [Function.update_self]
      have hm := Nat.mul_le_mul_left coefficient (hb (.inl 1))
      omega
    · rw [Function.update_of_ne hq]
      have h := hb q
      omega
  · exact counterPairRetreatTemplate_polynomial _ _ _ nextBudget

end ShiReversibleGenerator
