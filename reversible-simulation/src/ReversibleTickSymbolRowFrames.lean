import ReversibleTickSymbolRow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowTemplate_control_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (q : Fin 14) (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickSymbolRowTemplate tm stack inputStride bound backward).counters cs (.inl q) = cs (.inl q) :=
  tickCoordinateListTemplate_control_frame tm _ inputStride bound backward cs q hq

theorem tickSymbolRowTemplate_spare_frame (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (tickSymbolRowTemplate tm stack inputStride bound backward).counters cs (tickTraversalSpare tm j) =
      cs (tickTraversalSpare tm j) :=
  tickCoordinateListTemplate_spare_frame tm _ inputStride bound backward cs j

theorem tickSymbolRowTemplate_ready_preserved (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm)
      ((tickSymbolRowTemplate tm stack inputStride bound backward).counters cs) :=
  tickCoordinateListTemplate_ready_preserved tm _ inputStride bound backward cs hr

theorem tickSymbolRowTemplate_polynomial (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (tickSymbolRowTemplate tm stack inputStride strideBound backward).PolynomiallyTimed bound :=
  (tickSymbolRowTemplate_polynomial_certificate tm stack inputStride strideBound backward bound).2

noncomputable def tickSymbolRowPayload (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (input capacity outputBase position : Nat) : List Bool :=
  ((if backward then (tickSymbolOrder tm).reverse else tickSymbolOrder tm).map (fun a =>
    tickCoordinateSymbolicPayload tm (.inr (stack, a)) inputStride bound backward input capacity outputBase position)).flatten

theorem tickSymbolRowTemplate_payload_eq (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowTemplate tm stack inputStride bound backward).bytes cs =
      tickSymbolRowPayload tm stack inputStride bound backward (cs (.inl 0)) (cs (.inl 1))
        (cs (tickTraversalSpare tm 2)) (cs (.inl 2)) :=
  tickSymbolRowTemplate_payload tm stack inputStride bound backward cs

end ShiReversibleGenerator
