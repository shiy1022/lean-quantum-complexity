import ReversibleDescendingTemplateFrames
import ReversibleTickStackTraversalClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowAscendingBody_control_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (q : Fin 14) (h2 : q ≠ 2) (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickSymbolRowAscendingBody tm stack inputStride strideBound backward).counters cs (.inl q)=cs (.inl q) := by
  let after := (tickSymbolRowTemplate tm stack inputStride strideBound backward).counters cs
  change Function.update after (.inl 2) (after (.inl 2)+1) (.inl q)=_
  rw [Function.update_of_ne (by simpa using h2)]
  exact tickSymbolRowTemplate_control_frame tm stack inputStride strideBound backward cs q hq

theorem tickSymbolRowDescendingTemplate_control_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (q : Fin 14) (h2 : q ≠ 2) (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)).counters cs (.inl q)=cs (.inl q) :=
  descendingProgramTemplate_other_frame _ _ _ (by simpa using h2)
    (fun t => tickSymbolRowTemplate_control_frame tm stack inputStride strideBound backward t q hq) cs

theorem tickSymbolRowAscendingTemplate_control_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (q : Fin 14) (h2 : q ≠ 2) (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).counters cs (.inl q)=cs (.inl q) :=
  descendingProgramTemplate_other_frame _ _ _ (by simp [tickTraversalSpare])
    (fun t => tickSymbolRowAscendingBody_control_frame tm stack inputStride strideBound backward t q h2 hq) cs

theorem tickSymbolRowDescendingTemplate_spare_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound backward) (.inl 2)).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) :=
  descendingProgramTemplate_other_frame _ _ _ (by simp [tickTraversalSpare])
    (fun t => tickSymbolRowTemplate_spare_frame tm stack inputStride strideBound backward t j) cs

theorem tickSymbolRowAscendingTemplate_spare_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (j : Fin 8) (hj : j ≠ 0) :
    (tickSymbolRowAscendingTemplate tm stack inputStride strideBound backward).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) :=
  descendingProgramTemplate_other_frame _ _ _ (by
    intro h
    apply hj
    have hv := congrArg (fun r : FixedLeafRegister (tickTraversalSupply tm) => r.elim (fun _ => 0) Fin.val) h
    simp only [tickTraversalSpare,Sum.elim_inr] at hv
    apply Fin.ext
    omega)
    (fun t => tickSymbolRowAscendingBody_spare_frame tm stack inputStride strideBound backward t j) cs

end ShiReversibleGenerator
