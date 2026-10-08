import ReversibleTickResourcePreludeRun

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Actual prelude projection recovers the exact runtime raw/time/capacity/end metadata. -/
theorem tickResourcePrelude_metadata (tm : Turing.FinTM2) (n budget : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hpull : ∀ r,cs (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r) :
    cs (.inl 0)=n ∧ cs (.inl 1)=budget ∧ cs (.inl 2)=n+budget*machinePushBound tm+1 ∧
      cs (.inl 11)=n+18*configurationWidth tm (n+budget*machinePushBound tm+1)+
        budget*(configurationWidth tm (n+budget*machinePushBound tm+1)*(tickSizeBound tm+1)) ∧
      cs (.inl 5)=0 ∧ cs (.inl 6)=0 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [workspaceTickRegister,operationResult,workspaceOperations,GeneratorOperation.apply,
      AffineAtom.apply,workspaceInitial] using hpull 0
  · simpa [workspaceTickRegister,operationResult,workspaceOperations,GeneratorOperation.apply,
      AffineAtom.apply,workspaceInitial] using hpull 1
  · simpa [workspaceTickRegister,operationResult,workspaceOperations,GeneratorOperation.apply,
      AffineAtom.apply,workspaceInitial] using hpull 2
  · have h := hpull 11
    have hf : workspaceTickRegister tm 11=(.inl 11 : FixedLeafRegister (tickTraversalSupply tm)) := by
      simp [workspaceTickRegister]
    rw [hf,workspaceResult_prepared] at h
    simpa only [Nat.mul_comm 18 (configurationWidth tm (n+budget*machinePushBound tm+1))] using h
  · have h := hpull 5
    have hf : workspaceTickRegister tm 5=(.inl 5 : FixedLeafRegister (tickTraversalSupply tm)) := by
      simp [workspaceTickRegister]
    rw [hf,workspaceResult_scratch] at h
    exact h
  · have h := hpull 6
    have hf : workspaceTickRegister tm 6=(.inl 6 : FixedLeafRegister (tickTraversalSupply tm)) := by
      simp [workspaceTickRegister]
    rw [hf,workspaceResult_buffer] at h
    exact h

/-- The two high prelude registers are unused and leave the retained raw/time spare addresses zero. -/
theorem tickResourcePrelude_high_spares (tm : Turing.FinTM2) (n budget : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hpull : ∀ r,cs (workspaceTickRegister tm r)=
      operationResult (workspaceOperations tm) (workspaceInitial tm n budget) r) :
    cs (tickTraversalSpare tm 6)=0 ∧ cs (tickTraversalSpare tm 7)=0 := by
  have h6 := hpull 14
  have h7 := hpull 15
  rw [(workspaceTickRegister_high tm).1] at h6
  rw [(workspaceTickRegister_high tm).2] at h7
  constructor
  · simpa [operationResult,workspaceOperations,GeneratorOperation.apply,AffineAtom.apply,workspaceInitial] using h6
  · simpa [operationResult,workspaceOperations,GeneratorOperation.apply,AffineAtom.apply,workspaceInitial] using h7

end ShiReversibleGenerator
