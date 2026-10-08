import ReversibleCounterRegisterInjection
import ReversibleResourcePrelude
import ReversibleTickForwardStepFrames

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The prelude's fourteen control registers and two unused high registers fit the fixed emitter file. -/
noncomputable def workspaceTickRegister (tm : Turing.FinTM2) (r : WorkspaceRegister) :
    FixedLeafRegister (tickTraversalSupply tm) :=
  if hr : r.val < 14 then .inl ⟨r.val,hr⟩
  else tickTraversalSpare tm ⟨r.val-8,by have h := r.isLt; omega⟩

theorem workspaceTickRegister_injective (tm : Turing.FinTM2) : Function.Injective (workspaceTickRegister tm) := by
  intro a b h
  by_cases ha : a.val < 14
  · by_cases hb : b.val < 14
    · simp only [workspaceTickRegister,ha,hb,dite_true] at h
      have hv := congrArg Fin.val (Sum.inl.inj h)
      exact Fin.ext hv
    · simp [workspaceTickRegister,ha,hb,tickTraversalSpare] at h
  · by_cases hb : b.val < 14
    · simp [workspaceTickRegister,ha,hb,tickTraversalSpare] at h
    · simp only [workspaceTickRegister,ha,hb,dite_false] at h
      have hv := congrArg Fin.val (tickTraversalSpare_injective tm h)
      simp only at hv
      apply Fin.ext
      omega

theorem workspaceTickRegister_zero (tm : Turing.FinTM2) :
    workspaceTickRegister tm 0=(.inl 0 : FixedLeafRegister (tickTraversalSupply tm)) := by
  simp [workspaceTickRegister]

theorem workspaceTickRegister_high (tm : Turing.FinTM2) :
    workspaceTickRegister tm 14=tickTraversalSpare tm 6 ∧
    workspaceTickRegister tm 15=tickTraversalSpare tm 7 := by
  simp [workspaceTickRegister]

noncomputable def tickResourceInitial (tm : Turing.FinTM2) (n : Nat) :
    FixedLeafRegister (tickTraversalSupply tm) → Nat := fun q => if q=.inl 0 then n else 0

/-- Only raw length is nonzero in the actual ambient starting register file. -/
theorem tickResourceInitial_pull (tm : Turing.FinTM2) (n : Nat) :
    (fun r => tickResourceInitial tm n (workspaceTickRegister tm r))=resourceBudgetState n 0 := by
  funext r
  by_cases hr : r=0
  · subst r
    simp [tickResourceInitial,workspaceTickRegister_zero,resourceBudgetState]
  · have hf : workspaceTickRegister tm r ≠ .inl 0 := by
      intro h
      exact hr (workspaceTickRegister_injective tm (h.trans (workspaceTickRegister_zero tm).symm))
    simp [tickResourceInitial,hf,resourceBudgetState,hr]

end ShiReversibleGenerator
