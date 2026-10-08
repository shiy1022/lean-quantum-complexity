import ReversibleTickInverseAdvanceStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickInverseAdvanceStepTemplate_input (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).counters cs (.inl 0)=cs (tickTraversalSpare tm 2)+bound := by
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound true).counters cs) (.inl 0)=_
  rw [tickWindowAdvanceTemplate_counters]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 2),Function.update_self]
  rw [tickForestTemplate_spare_frame tm inputStride bound true cs 2 (by decide)]

theorem tickInverseAdvanceStepTemplate_output (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).counters cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 2)+configurationWidth tm (cs (.inl 1))*(bound+1) := by
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound true).counters cs) (tickTraversalSpare tm 2)=_
  rw [tickWindowAdvanceTemplate_counters,Function.update_self,
    tickForestTemplate_spare_frame tm inputStride bound true cs 2 (by decide),
    tickForestTemplate_control_frame tm inputStride bound true cs 1 (by decide) (by decide)]

theorem tickInverseAdvanceStepTemplate_count (tm : Turing.FinTM2) (inputStride bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInverseAdvanceStepTemplate tm inputStride bound).counters cs (.inl 9)=cs (.inl 9)+tickForestLayerCount tm (cs (.inl 1)) := by
  change (tickWindowAdvanceTemplate tm bound).counters ((tickForestTemplate tm inputStride bound true).counters cs) (.inl 9)=_
  rw [tickWindowAdvanceTemplate_counters]
  simp only [Function.update_of_ne (by simp [tickTraversalSpare] :
    (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ tickTraversalSpare tm 2),
    Function.update_of_ne (by simp : (Sum.inl (9 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 0)]
  exact tickForestTemplate_count tm inputStride bound true cs

end ShiReversibleGenerator
