import ReversibleProgramTemplateListBudget
import ReversibleTickBodyCounterBudget
import ReversibleTickCoordinatePayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickCoordinateListTemplate (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) :=
  listProgramTemplate (kinds.map (fun kind => stridedTickCoordinateBody tm kind inputStride bound backward))

theorem tickCoordinateListTemplate_embeds (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) :
    (tickCoordinateListTemplate tm kinds inputStride bound backward).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  obtain ⟨kind, hk, rfl⟩ := List.mem_map.mp hp
  exact stridedTickCoordinateBody_embeds tm kind inputStride bound backward

theorem tickCoordinateListTemplate_run (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) :
    (tickCoordinateListTemplate tm kinds inputStride bound backward).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    obtain ⟨kind, hk, rfl⟩ := List.mem_map.mp hp
    exact stridedTickCoordinateBody_embeds tm kind inputStride bound backward
  · intro p hp
    obtain ⟨kind, hk, rfl⟩ := List.mem_map.mp hp
    exact stridedTickCoordinateBody_run tm kind inputStride bound backward

theorem tickCoordinateListTemplate_ready (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    (tickCoordinateListTemplate tm kinds inputStride bound backward).ready cs := by
  induction kinds generalizing cs with
  | nil => trivial
  | cons kind kinds ih =>
    exact ⟨stridedTickCoordinateBody_ready tm kind inputStride bound backward cs hr,
      ih _ (stridedTickCoordinateBody_ready_preserved tm kind inputStride bound backward cs hr)⟩

theorem tickCoordinateListTemplate_control_frame (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (q : Fin 14) (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickCoordinateListTemplate tm kinds inputStride bound backward).counters cs (.inl q) = cs (.inl q) := by
  induction kinds generalizing cs with
  | nil => rfl
  | cons kind kinds ih =>
    change (tickCoordinateListTemplate tm kinds inputStride bound backward).counters
      ((stridedTickCoordinateBody tm kind inputStride bound backward).counters cs) (.inl q) = _
    rw [ih, stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs q hq]

theorem tickCoordinateListTemplate_spare_frame (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (tickCoordinateListTemplate tm kinds inputStride bound backward).counters cs (tickTraversalSpare tm j) =
      cs (tickTraversalSpare tm j) := by
  induction kinds generalizing cs with
  | nil => rfl
  | cons kind kinds ih =>
    change (tickCoordinateListTemplate tm kinds inputStride bound backward).counters
      ((stridedTickCoordinateBody tm kind inputStride bound backward).counters cs) (tickTraversalSpare tm j) = _
    rw [ih, stridedTickCoordinateBody_spare_frame]

theorem tickCoordinateListTemplate_ready_preserved (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm)
      ((tickCoordinateListTemplate tm kinds inputStride bound backward).counters cs) := by
  induction kinds generalizing cs with
  | nil => exact hr
  | cons kind kinds ih =>
    exact ih _ (stridedTickCoordinateBody_ready_preserved tm kind inputStride bound backward cs hr)

theorem tickCoordinateListTemplate_polynomial_certificate (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride strideBound : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (tickCoordinateListTemplate tm kinds inputStride strideBound backward).CounterBound bound ∧
    (tickCoordinateListTemplate tm kinds inputStride strideBound backward).PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp budget
    obtain ⟨kind, hk, rfl⟩ := List.mem_map.mp hp
    exact stridedTickCoordinateBody_polynomial tm kind inputStride strideBound backward budget
  · intro p hp budget
    obtain ⟨kind, hk, rfl⟩ := List.mem_map.mp hp
    exact stridedTickCoordinateBody_counter_bound tm kind inputStride strideBound backward budget

theorem tickCoordinateListTemplate_payload (tm : Turing.FinTM2) (kinds : List (TickTreeKind tm))
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickCoordinateListTemplate tm kinds inputStride bound backward).bytes cs =
      (kinds.reverse.map (fun kind => tickCoordinateSymbolicPayload tm kind inputStride bound backward
        (cs (.inl 0)) (cs (.inl 1)) (cs (tickTraversalSpare tm 2)) (cs (.inl 2)))).flatten := by
  induction kinds generalizing cs with
  | nil => simp [tickCoordinateListTemplate, listProgramTemplate, identityProgramTemplate]
  | cons kind kinds ih =>
    change (tickCoordinateListTemplate tm kinds inputStride bound backward).bytes
      ((stridedTickCoordinateBody tm kind inputStride bound backward).counters cs) ++
      (stridedTickCoordinateBody tm kind inputStride bound backward).bytes cs = _
    rw [ih, stridedTickCoordinateBody_symbolic_payload,
      stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs 0 (by decide),
      stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs 1 (by decide),
      stridedTickCoordinateBody_spare_frame tm kind inputStride bound backward cs 2,
      stridedTickCoordinateBody_control_frame tm kind inputStride bound backward cs 2 (by decide)]
    simp [List.reverse_cons, List.map_append, List.flatten_append]

end ShiReversibleGenerator
