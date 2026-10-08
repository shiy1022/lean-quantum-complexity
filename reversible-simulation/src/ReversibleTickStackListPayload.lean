import ReversibleTickStackListClock
import ReversibleTickStackTraversalPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Bytes are prepended, so sequential stack execution reverses the order of stack blocks. -/
theorem tickStackListTemplate_payload (tm : Turing.FinTM2) (stackOrder : List tm.K)
    (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickStackListTemplate tm stackOrder inputStride strideBound backward).bytes cs =
      (stackOrder.reverse.map (fun k =>
        if backward then tickSymbolRowAscendingBytes tm k inputStride strideBound backward
          (cs (.inl 0)) (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) 0 (cs (.inl 1))
        else tickSymbolRowDescendingBytes tm k inputStride strideBound backward
          (cs (.inl 0)) (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) (cs (.inl 1)))).flatten := by
  induction stackOrder generalizing cs with
  | nil => rfl
  | cons k stackOrder ih =>
    let after := (tickStackTraversalTemplate tm k inputStride strideBound backward).counters cs
    have h0 : after (.inl 0)=cs (.inl 0) :=
      tickStackTraversalTemplate_control_frame tm k inputStride strideBound backward cs 0 (by decide) (by decide)
    have h1 : after (.inl 1)=cs (.inl 1) :=
      tickStackTraversalTemplate_control_frame tm k inputStride strideBound backward cs 1 (by decide) (by decide)
    have h2 : after (tickTraversalSpare tm 2)=cs (tickTraversalSpare tm 2) :=
      tickStackTraversalTemplate_spare_frame tm k inputStride strideBound backward cs 2 (by decide)
    change (tickStackListTemplate tm stackOrder inputStride strideBound backward).bytes after ++
      (tickStackTraversalTemplate tm k inputStride strideBound backward).bytes cs = _
    rw [ih,tickStackTraversalTemplate_payload]
    simp only [h0,h1,h2,List.reverse_cons,List.map_append,List.map_singleton,List.flatten_append,
      List.flatten_cons,List.flatten_nil,List.append_nil]

end ShiReversibleGenerator
