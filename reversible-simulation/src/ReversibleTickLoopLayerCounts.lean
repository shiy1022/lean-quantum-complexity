import ReversibleTickSymbolicLayerCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickSymbolRowDescendingLayers (tm : Turing.FinTM2) (stack : tm.K) (capacity : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => tickSymbolRowDescendingLayers tm stack capacity k+tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) capacity k

noncomputable def tickSymbolRowAscendingLayers (tm : Turing.FinTM2) (stack : tm.K) (capacity : Nat) : Nat → Nat → Nat
  | _,0 => 0
  | position,k+1 => tickSymbolRowAscendingLayers tm stack capacity (position+1) k+
      tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) capacity position

theorem tickSymbolRowAscendingBody_symbolic_count (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowAscendingBody tm stack inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) (cs (.inl 1)) (cs (.inl 2)) := by
  change Function.update ((tickSymbolRowTemplate tm stack inputStride bound backward).counters cs)
    (.inl 2) (((tickSymbolRowTemplate tm stack inputStride bound backward).counters cs) (.inl 2)+1) (.inl 9)=_
  rw [Function.update_of_ne (by simp),tickSymbolRowTemplate_symbolic_count]

theorem tickSymbolRowDescendingResult_count {L : Type} (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) L) :
    (descendingResult (templateDescendingBody (tickSymbolRowTemplate tm stack inputStride bound backward) (.inl 2)) count s).counters (.inl 9)=
      s.counters (.inl 9)+tickSymbolRowDescendingLayers tm stack (s.counters (.inl 1)) count := by
  let p := tickSymbolRowTemplate tm stack inputStride bound backward
  induction count generalizing s with
  | zero => simp [descendingResult,tickSymbolRowDescendingLayers]
  | succ k ih =>
    let t := templateDescendingBody p (.inl 2) k s
    have hcap : t.counters (.inl 1)=s.counters (.inl 1) := by
      change p.counters (Function.update s.counters (.inl 2) k) (.inl 1)=_
      rw [tickSymbolRowTemplate_control_frame tm stack inputStride bound backward _ 1 (by decide)]
      simp
    have hcount : t.counters (.inl 9)=s.counters (.inl 9)+tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) (s.counters (.inl 1)) k := by
      change p.counters (Function.update s.counters (.inl 2) k) (.inl 9)=_
      rw [tickSymbolRowTemplate_symbolic_count]
      simp
    change (descendingResult (templateDescendingBody p (.inl 2)) k t).counters (.inl 9)=_
    rw [ih,hcap,hcount]
    simp only [tickSymbolRowDescendingLayers]
    omega

theorem tickSymbolRowAscendingResult_count {L : Type} (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm)) L) :
    (descendingResult (templateDescendingBody (tickSymbolRowAscendingBody tm stack inputStride bound backward) (tickTraversalSpare tm 0)) count s).counters (.inl 9)=
      s.counters (.inl 9)+tickSymbolRowAscendingLayers tm stack (s.counters (.inl 1)) (s.counters (.inl 2)) count := by
  let p := tickSymbolRowAscendingBody tm stack inputStride bound backward
  let remaining := tickTraversalSpare tm 0
  induction count generalizing s with
  | zero => simp [descendingResult,tickSymbolRowAscendingLayers]
  | succ k ih =>
    let t := templateDescendingBody p remaining k s
    have hcap : t.counters (.inl 1)=s.counters (.inl 1) := by
      change p.counters (Function.update s.counters remaining k) (.inl 1)=_
      rw [tickSymbolRowAscendingBody_capacity]
      simp [remaining,tickTraversalSpare]
    have hpos : t.counters (.inl 2)=s.counters (.inl 2)+1 := by
      change p.counters (Function.update s.counters remaining k) (.inl 2)=_
      rw [tickSymbolRowAscendingBody_position]
      simp [remaining,tickTraversalSpare]
    have hcount : t.counters (.inl 9)=s.counters (.inl 9)+tickCoordinateListSymbolicLayers tm (tickSymbolRowKinds tm stack) (s.counters (.inl 1)) (s.counters (.inl 2)) := by
      change p.counters (Function.update s.counters remaining k) (.inl 9)=_
      rw [tickSymbolRowAscendingBody_symbolic_count]
      simp [remaining,tickTraversalSpare]
    change (descendingResult (templateDescendingBody p remaining) k t).counters (.inl 9)=_
    rw [ih,hcap,hpos,hcount]
    simp only [tickSymbolRowAscendingLayers]
    omega

theorem tickSymbolRowDescendingTemplate_count (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (descendingProgramTemplate (tickSymbolRowTemplate tm stack inputStride bound backward) (.inl 2)).counters cs (.inl 9)=
      cs (.inl 9)+tickSymbolRowDescendingLayers tm stack (cs (.inl 1)) (cs (.inl 2)) := by
  rw [descendingProgramTemplate_result_counters _ _ cs [] (none : Option Unit)]
  rw [Function.update_of_ne (by simp)]
  exact tickSymbolRowDescendingResult_count tm stack inputStride bound backward _ ⟨none,cs,[]⟩

theorem tickSymbolRowAscendingTemplate_count (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickSymbolRowAscendingTemplate tm stack inputStride bound backward).counters cs (.inl 9)=
      cs (.inl 9)+tickSymbolRowAscendingLayers tm stack (cs (.inl 1)) (cs (.inl 2)) (cs (tickTraversalSpare tm 0)) := by
  unfold tickSymbolRowAscendingTemplate
  rw [descendingProgramTemplate_result_counters _ _ cs [] (none : Option Unit)]
  rw [Function.update_of_ne (by simp [tickTraversalSpare])]
  exact tickSymbolRowAscendingResult_count tm stack inputStride bound backward _ ⟨none,cs,[]⟩

end ShiReversibleGenerator
