import ReversibleCounterAffineProgramTemplates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def tickWidthSlope (tm : Turing.FinTM2) : Nat :=
  Fintype.card tm.K*Fintype.card (Option (MachineSymbol tm))
noncomputable def tickWidthOffset (tm : Turing.FinTM2) : Nat :=
  Fintype.card (Option tm.Λ)+Fintype.card tm.σ

theorem tickWidth_affine (tm : Turing.FinTM2) (capacity : Nat) :
    configurationWidth tm capacity=tickWidthSlope tm*capacity+tickWidthOffset tm := by
  simp only [configurationWidth,tickWidthSlope,tickWidthOffset]
  ring

noncomputable def tickWindowAdvanceAtom (tm : Turing.FinTM2) (bound : Nat) :
    AffineAtom (FixedLeafRegister (tickTraversalSupply tm)) :=
  ⟨.inl 1,tickTraversalSpare tm 2,tickWidthOffset tm*(bound+1),tickWidthSlope tm*(bound+1)⟩

/-- The actual finite program selects the just-computed result window and advances to fresh targets. -/
noncomputable def tickWindowAdvanceTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  sequenceProgramTemplate
    (counterAffineCopyProgramTemplate (tickTraversalSpare tm 2) (.inl 0) (.inl 5) bound 1 0)
    (counterAffineAccumulationProgramTemplate (tickWindowAdvanceAtom tm bound) (.inl 5))

theorem tickWindowAdvanceTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickWindowAdvanceTemplate tm bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
    (counterAffineAccumulationProgramTemplate_embeds _ _)

theorem tickWindowAdvanceTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickWindowAdvanceTemplate tm bound).Runs := by
  apply sequenceProgramTemplate_run
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by simp [tickTraversalSpare])
      (by simp [tickTraversalSpare]) (by simp)
  · apply counterAffineAccumulationProgramTemplate_run
    simp [AffineAtom.Valid,tickWindowAdvanceAtom,tickTraversalSpare]

theorem tickWindowAdvanceTemplate_counters (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickWindowAdvanceTemplate tm bound).counters cs =
      Function.update (Function.update cs (.inl 0) (cs (tickTraversalSpare tm 2)+bound)) (tickTraversalSpare tm 2)
        (cs (tickTraversalSpare tm 2)+configurationWidth tm (cs (.inl 1))*(bound+1)) := by
  unfold tickWindowAdvanceTemplate sequenceProgramTemplate counterAffineCopyProgramTemplate
    counterAffineAccumulationProgramTemplate tickWindowAdvanceAtom AffineAtom.apply
  simp only [Nat.one_mul,Nat.sub_zero]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (tickTraversalSpare tm 2 : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 0),
    Function.update_of_ne (by simp : (Sum.inl (1 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 0)]
  rw [tickWidth_affine]
  congr 1
  ring

theorem tickWindowAdvanceTemplate_ready (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickWindowAdvanceTemplate tm bound).ready cs ↔ cs (.inl 5)=0 := by
  simp [tickWindowAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate]

theorem tickWindowAdvanceTemplate_bytes (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickWindowAdvanceTemplate tm bound).bytes cs=[] := rfl

theorem tickWindowAdvanceTemplate_polynomial (tm : Turing.FinTM2) (bound : Nat) (budget : Polynomial Nat) :
    (tickWindowAdvanceTemplate tm bound).PolynomiallyTimed budget := by
  apply sequenceProgramTemplate_polynomial _ _ budget (budget+Polynomial.C bound)
  · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ budget
  · intro n cs hb _ q
    change Function.update cs (.inl 0) (1*cs (tickTraversalSpare tm 2)+bound-0) q ≤ _
    by_cases hq : q=Sum.inl 0
    · subst q
      simpa only [Function.update_self,Nat.one_mul,Nat.sub_zero,Polynomial.eval_add,Polynomial.eval_C]
        using Nat.add_le_add_right (hb (tickTraversalSpare tm 2)) bound
    · rw [Function.update_of_ne hq]
      simpa only [Polynomial.eval_add,Polynomial.eval_C] using (hb q).trans (Nat.le_add_right _ _)
  · exact counterAffineAccumulationProgramTemplate_polynomial _ _ _

end ShiReversibleGenerator
