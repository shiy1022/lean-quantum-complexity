import ReversibleTickLoopTemplateFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickStackTraversalTemplate_control_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (q : Fin 14) (h2 : q ≠ 2) (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).counters cs (.inl q)=cs (.inl q) := by
  have hn : (Sum.inl q : FixedLeafRegister (tickTraversalSupply tm)) ∉ [.inl 2,tickTraversalSpare tm 0] := by
    simp [tickTraversalSpare,h2]
  cases backward with
  | false =>
    let after := (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs
    change cleanupCounters [.inl 2,tickTraversalSpare tm 0]
      ((descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound false) (.inl 2)).counters after) (.inl q)=_
    rw [cleanupCounters_apply,if_neg hn,tickSymbolRowDescendingTemplate_control_frame tm stack inputStride strideBound false after q h2 hq]
    simp [after,counterCopyProgramTemplate,h2]
  | true =>
    let cleared := (cleanupProgramTemplate [.inl 2]).counters cs
    let after := (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters cleared
    change cleanupCounters [.inl 2,tickTraversalSpare tm 0]
      ((tickSymbolRowAscendingTemplate tm stack inputStride strideBound true).counters after) (.inl q)=_
    rw [cleanupCounters_apply,if_neg hn,tickSymbolRowAscendingTemplate_control_frame tm stack inputStride strideBound true after q h2 hq]
    simp [after,cleared,counterCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters,tickTraversalSpare,h2]

theorem tickStackTraversalTemplate_spare_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (j : Fin 8) (hj : j ≠ 0) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) := by
  have hsp : tickTraversalSpare tm j ≠ tickTraversalSpare tm 0 := by
    intro h
    apply hj
    have hv := congrArg (fun r : FixedLeafRegister (tickTraversalSupply tm) => r.elim (fun _ => 0) Fin.val) h
    simp only [tickTraversalSpare,Sum.elim_inr] at hv
    apply Fin.ext
    omega
  have hn : tickTraversalSpare tm j ∉ [.inl 2,tickTraversalSpare tm 0] := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · simpa [tickTraversalSpare] using h
    · exact hsp (List.mem_singleton.mp h)
  cases backward with
  | false =>
    let after := (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs
    change cleanupCounters [.inl 2,tickTraversalSpare tm 0]
      ((descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound false) (.inl 2)).counters after) (tickTraversalSpare tm j)=_
    rw [cleanupCounters_apply,if_neg hn,tickSymbolRowDescendingTemplate_spare_frame tm stack inputStride strideBound false after j]
    simp [after,counterCopyProgramTemplate,tickTraversalSpare]
  | true =>
    let cleared := (cleanupProgramTemplate [.inl 2]).counters cs
    let after := (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters cleared
    change cleanupCounters [.inl 2,tickTraversalSpare tm 0]
      ((tickSymbolRowAscendingTemplate tm stack inputStride strideBound true).counters after) (tickTraversalSpare tm j)=_
    rw [cleanupCounters_apply,if_neg hn,tickSymbolRowAscendingTemplate_spare_frame tm stack inputStride strideBound true after j hj]
    change Function.update cleared (tickTraversalSpare tm 0) (cleared (.inl 1)) (tickTraversalSpare tm j)=_
    rw [Function.update_of_ne hsp]
    change cleanupCounters [.inl 2] cs (tickTraversalSpare tm j)=_
    rw [cleanupCounters_apply,if_neg (by simp [tickTraversalSpare])]

theorem tickStackTraversalTemplate_position_zero (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).counters cs (.inl 2)=0 := by
  cases backward <;> simp [tickStackTraversalTemplate,sequenceProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply]

theorem tickStackTraversalTemplate_remaining_zero (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).counters cs (tickTraversalSpare tm 0)=0 := by
  cases backward <;> simp [tickStackTraversalTemplate,sequenceProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply]

end ShiReversibleGenerator
