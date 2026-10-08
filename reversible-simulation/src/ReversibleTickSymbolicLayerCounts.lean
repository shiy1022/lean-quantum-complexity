import ReversibleTickForestPayloadAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickCoordinateSymbolicLayers (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (capacity position : Nat) : Nat :=
  formulaElementaryLayers ((tickTreeForKind tm kind).eval (TickIndexGuard.eval capacity position))+1

noncomputable def tickCoordinateListSymbolicLayers (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (capacity position : Nat) : Nat :=
  (kinds.map (fun kind => tickCoordinateSymbolicLayers tm kind capacity position)).sum

theorem stridedTickCoordinateBody_symbolic_count (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (stridedTickCoordinateBody tm kind inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickCoordinateSymbolicLayers tm kind (cs (.inl 1)) (cs (.inl 2)) := by
  change (stridedSharedFixedGuardedEmitter (tickTraversalSupply tm) (tickTreeForKind tm kind) inputStride backward).counters
    (tickOutputPreparationCounters tm kind bound cs) (.inl 9)=_
  rw [stridedSharedFixedGuardedEmitter_count]
  simp [tickCoordinateSymbolicLayers,tickOutputPreparationCounters,Nat.add_assoc]

theorem tickCoordinateListTemplate_symbolic_count (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickCoordinateListTemplate tm kinds inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickCoordinateListSymbolicLayers tm kinds (cs (.inl 1)) (cs (.inl 2)) := by
  induction kinds generalizing cs with
  | nil => simp [tickCoordinateListTemplate,listProgramTemplate,identityProgramTemplate,tickCoordinateListSymbolicLayers]
  | cons kind kinds ih =>
    change (tickCoordinateListTemplate tm kinds inputStride bound backward).counters
      ((stridedTickCoordinateBody tm kind inputStride bound backward).counters cs) (.inl 9)=_
    rw [ih,stridedTickCoordinateBody_symbolic_count,
      stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs 1 (by decide),
      stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs 2 (by decide)]
    simp [tickCoordinateListSymbolicLayers,Nat.add_assoc]

theorem tickSymbolRowTemplate_symbolic_count (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowTemplate tm stack inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) (cs (.inl 1)) (cs (.inl 2)) := by
  unfold tickSymbolRowTemplate
  rw [tickCoordinateListTemplate_symbolic_count]
  cases backward <;> simp [tickCoordinateListSymbolicLayers,List.map_reverse]

theorem tickCoordinateSymbolicLayers_bounded (tm : Turing.FinTM2) (capacity : Nat) (i : Fin capacity) (kind : TickTreeKind tm) :
    tickCoordinateSymbolicLayers tm kind capacity i.val =
      formulaElementaryLayers (boundedTickFormulaForKind tm capacity i kind)+1 := by
  have h := congrArg formulaElementaryLayers (tickTreeForKind_formula_agreement tm capacity i kind)
  simpa only [tickCoordinateSymbolicLayers,DecisionTree.evaluate,formulaElementaryLayers_rename] using congrArg (fun n => n+1) h

end ShiReversibleGenerator
