import ReversibleTickStackTraversalReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The complete stack program prints the prescribed forest order, independent of old control-counter values. -/
theorem tickStackTraversalTemplate_payload (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickStackTraversalTemplate tm stack inputStride strideBound backward).bytes cs =
      if backward then tickSymbolRowAscendingBytes tm stack inputStride strideBound backward
        (cs (.inl 0)) (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) 0 (cs (.inl 1))
      else tickSymbolRowDescendingBytes tm stack inputStride strideBound backward
        (cs (.inl 0)) (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) (cs (.inl 1)) := by
  cases backward with
  | false =>
    let after := (counterCopyProgramTemplate (.inl 1) (.inl 2) (.inl 5)).counters cs
    change (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride strideBound false) (.inl 2)).bytes after ++ [] = _
    rw [tickSymbolRowDescendingTemplate_payload]
    simp [after,counterCopyProgramTemplate,tickTraversalSpare]
  | true =>
    let cleared := (cleanupProgramTemplate [.inl 2]).counters cs
    let after := (counterCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 0) (.inl 5)).counters cleared
    change ((tickSymbolRowAscendingTemplate tm stack inputStride strideBound true).bytes after ++ []) ++ [] = _
    rw [tickSymbolRowAscendingTemplate_payload]
    simp [after,cleared,counterCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters,tickTraversalSpare,Fin.ext_iff]

end ShiReversibleGenerator
