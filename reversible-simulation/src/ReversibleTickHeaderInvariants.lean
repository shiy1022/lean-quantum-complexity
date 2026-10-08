import ReversibleTickForestTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickHeaderTemplate_control_frame (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14) (h2 : q ≠ 2)
    (hq : q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 12 ∧ q ≠ 13) :
    (tickHeaderTemplate tm inputStride strideBound backward).counters cs (.inl q)=cs (.inl q) := by
  change (tickCoordinateListTemplate tm _ inputStride strideBound backward).counters
    (cleanupCounters [.inl 2] cs) (.inl q)=_
  rw [tickCoordinateListTemplate_control_frame tm _ inputStride strideBound backward _ q hq]
  rw [cleanupCounters_apply,if_neg (by simp [h2])]

theorem tickHeaderTemplate_spare_frame (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8) :
    (tickHeaderTemplate tm inputStride strideBound backward).counters cs (tickTraversalSpare tm j)=
      cs (tickTraversalSpare tm j) := by
  change (tickCoordinateListTemplate tm _ inputStride strideBound backward).counters
    (cleanupCounters [.inl 2] cs) (tickTraversalSpare tm j)=_
  rw [tickCoordinateListTemplate_spare_frame]
  rw [cleanupCounters_apply,if_neg (by simp [tickTraversalSpare])]

theorem tickHeaderSetup_ready (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) (cleanupCounters [.inl 2] cs) := by
  simpa [fixedGuardedEmitterReady,cleanupCounters_apply] using hr

theorem tickHeaderTemplate_ready (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    (tickHeaderTemplate tm inputStride strideBound backward).ready cs :=
  ⟨trivial,tickCoordinateListTemplate_ready tm _ inputStride strideBound backward _ (tickHeaderSetup_ready tm cs hr)⟩

theorem tickHeaderTemplate_ready_preserved (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm)
      ((tickHeaderTemplate tm inputStride strideBound backward).counters cs) :=
  tickCoordinateListTemplate_ready_preserved tm _ inputStride strideBound backward _ (tickHeaderSetup_ready tm cs hr)

/-- A nonempty capacity window suffices for the header's explicit position-zero setup. -/
theorem tickHeaderTemplate_final_bounds (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (wireBound : Nat) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hb : CounterBudget cs (.inl 9) wireBound) (hw : TickWindowBudget tm inputStride strideBound wireBound cs)
    (hc : 0 < cs (.inl 1)) (hsize : tickSizeBound tm ≤ strideBound) :
    let final := (tickHeaderTemplate tm inputStride strideBound backward).counters cs
    CounterBudget final (.inl 9) wireBound ∧ TickWindowBudget tm inputStride strideBound wireBound final ∧
      final (.inl 9) ≤ cs (.inl 9)+(tickHeaderKinds tm).length*(37*tickSizeBound tm+1) := by
  let initial := cleanupCounters [.inl 2] cs
  let kinds := if backward then tickHeaderKinds tm else (tickHeaderKinds tm).reverse
  have hb' : CounterBudget initial (.inl 9) wireBound := hb.cleanup [.inl 2]
  have hw' : TickWindowBudget tm inputStride strideBound wireBound initial := by
    simpa [initial,TickWindowBudget,cleanupCounters_apply,tickTraversalSpare] using hw
  have hi : initial (.inl 2) < initial (.inl 1) := by
    simpa [initial,cleanupCounters_apply] using hc
  have hs := tickCoordinateListTemplate_static_budget tm kinds inputStride strideBound backward initial wireBound hb' hw' hi hsize
  have hl := tickCoordinateListTemplate_layer_bound tm kinds inputStride strideBound backward initial hi
  refine ⟨hs.1,hs.2,?_⟩
  cases backward <;> simpa [tickHeaderTemplate,sequenceProgramTemplate,cleanupProgramTemplate,initial,kinds,cleanupCounters_apply] using hl

theorem tickHeaderTemplate_position_zero (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickHeaderTemplate tm inputStride strideBound backward).counters cs (.inl 2)=0 := by
  change (tickCoordinateListTemplate tm _ inputStride strideBound backward).counters (cleanupCounters [.inl 2] cs) (.inl 2)=_
  rw [tickCoordinateListTemplate_control_frame tm _ inputStride strideBound backward _ 2 (by decide)]
  simp [cleanupCounters_apply]

end ShiReversibleGenerator
