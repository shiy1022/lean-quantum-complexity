import ReversibleTickCoordinateList

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def tickSymbolOrder (tm : Turing.FinTM2) : List (Option (MachineSymbol tm)) :=
  List.ofFn (Fintype.equivFin (Option (MachineSymbol tm))).symm

noncomputable def tickSymbolRowKinds (tm : Turing.FinTM2) (k : tm.K) : List (TickTreeKind tm) :=
  (tickSymbolOrder tm).map (fun a => .inr (k, a))

/-- Fixed symbol control sits inside runtime position traversal; execution order accounts for prepending. -/
noncomputable def tickSymbolRowTemplate (tm : Turing.FinTM2) (k : tm.K)
    (inputStride bound : Nat) (backward : Bool) :=
  tickCoordinateListTemplate tm (if backward then tickSymbolRowKinds tm k else (tickSymbolRowKinds tm k).reverse)
    inputStride bound backward

theorem tickSymbolRowTemplate_embeds (tm : Turing.FinTM2) (k : tm.K)
    (inputStride bound : Nat) (backward : Bool) :
    (tickSymbolRowTemplate tm k inputStride bound backward).Embeds :=
  tickCoordinateListTemplate_embeds tm _ inputStride bound backward

theorem tickSymbolRowTemplate_run (tm : Turing.FinTM2) (k : tm.K)
    (inputStride bound : Nat) (backward : Bool) :
    (tickSymbolRowTemplate tm k inputStride bound backward).Runs :=
  tickCoordinateListTemplate_run tm _ inputStride bound backward

theorem tickSymbolRowTemplate_ready (tm : Turing.FinTM2) (k : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    (tickSymbolRowTemplate tm k inputStride bound backward).ready cs :=
  tickCoordinateListTemplate_ready tm _ inputStride bound backward cs hr

theorem tickSymbolRowTemplate_polynomial_certificate (tm : Turing.FinTM2) (k : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (tickSymbolRowTemplate tm k inputStride strideBound backward).CounterBound bound ∧
    (tickSymbolRowTemplate tm k inputStride strideBound backward).PolynomiallyTimed bound :=
  tickCoordinateListTemplate_polynomial_certificate tm _ inputStride strideBound backward bound

theorem tickSymbolRowTemplate_payload (tm : Turing.FinTM2) (k : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowTemplate tm k inputStride bound backward).bytes cs =
      ((if backward then (tickSymbolOrder tm).reverse else tickSymbolOrder tm).map (fun a =>
        tickCoordinateSymbolicPayload tm (.inr (k, a)) inputStride bound backward (cs (.inl 0))
          (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) (cs (.inl 2)))).flatten := by
  unfold tickSymbolRowTemplate
  rw [tickCoordinateListTemplate_payload]
  cases backward <;> simp [tickSymbolRowKinds, List.map_map, Function.comp_def]

end ShiReversibleGenerator
