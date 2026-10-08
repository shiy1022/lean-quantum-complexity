import ReversibleTickCoordinatePayload
import ReversibleStridedTickAscendingTraversal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickCoordinateAscendingBytes (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (input capacity outputBase : Nat) : Nat → Nat → List Bool
  | _, 0 => []
  | position, k + 1 =>
      tickCoordinateAscendingBytes tm kind inputStride bound backward input capacity outputBase (position + 1) k ++
      tickCoordinateSymbolicPayload tm kind inputStride bound backward input capacity outputBase position

/-- Increasing actual traversal prepends coordinate blocks in reverse forest order. -/
theorem stridedTickAscendingResult_output (tm : Turing.FinTM2) (kind : TickTreeKind tm)
    (inputStride bound : Nat) (backward : Bool) (count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((stridedTickAscendingBody tm kind inputStride bound backward).Labels (Fin 3))) :
    let p := stridedTickAscendingBody tm kind inputStride bound backward
    let remaining := tickTraversalSpare tm 0
    (descendingResult (programDescendingBody p remaining) count s).output =
      tickCoordinateAscendingBytes tm kind inputStride bound backward (s.counters (.inl 0))
        (s.counters (.inl 1)) (s.counters (tickTraversalSpare tm 2)) (s.counters (.inl 2)) count ++ s.output := by
  let p := stridedTickAscendingBody tm kind inputStride bound backward
  let remaining := tickTraversalSpare tm 0
  induction count generalizing s with
  | zero => simp [descendingResult, tickCoordinateAscendingBytes]
  | succ k ih =>
    let t := programDescendingBody p remaining k s
    have h0 : t.counters (.inl 0) = s.counters (.inl 0) := by
      let after := (stridedTickCoordinateBody tm kind inputStride bound backward).counters
        (Function.update s.counters remaining k)
      change Function.update after (.inl 2) (after (.inl 2) + 1) (.inl 0) = _
      rw [Function.update_of_ne (by simp : (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 2)]
      dsimp only [after]
      rw [stridedTickCoordinateBody_control_frame tm kind inputStride bound backward _ 0 (by decide)]
      simp [remaining, tickTraversalSpare]
    have h1 : t.counters (.inl 1) = s.counters (.inl 1) := by
      change p.counters (Function.update s.counters remaining k) (.inl 1) = _
      rw [stridedTickAscendingBody_capacity]
      simp [remaining, tickTraversalSpare]
    have ho : t.counters (tickTraversalSpare tm 2) = s.counters (tickTraversalSpare tm 2) := by
      change p.counters (Function.update s.counters remaining k) (tickTraversalSpare tm 2) = _
      rw [stridedTickAscendingBody_spare_frame]
      have hn : tickTraversalSpare tm 2 ≠ remaining := by simp [remaining, tickTraversalSpare, Fin.ext_iff]
      simp [hn]
    have hp : t.counters (.inl 2) = s.counters (.inl 2) + 1 := by
      change p.counters (Function.update s.counters remaining k) (.inl 2) = _
      rw [stridedTickAscendingBody_position]
      simp [remaining, tickTraversalSpare]
    have hy : t.output = tickCoordinateSymbolicPayload tm kind inputStride bound backward
        (s.counters (.inl 0)) (s.counters (.inl 1)) (s.counters (tickTraversalSpare tm 2))
        (s.counters (.inl 2)) ++ s.output := by
      change p.bytes (Function.update s.counters remaining k) ++ s.output = _
      simp only [p, stridedTickAscendingBody, sequenceProgramTemplate, incrementProgramTemplate, List.nil_append]
      rw [stridedTickCoordinateBody_symbolic_payload]
      have hn : tickTraversalSpare tm 2 ≠ remaining := by simp [remaining, tickTraversalSpare, Fin.ext_iff]
      simp [remaining, tickTraversalSpare, hn, Fin.ext_iff]
    change (descendingResult (programDescendingBody p remaining) k t).output = _
    rw [ih, h0, h1, ho, hp, hy]
    simp only [tickCoordinateAscendingBytes, List.append_assoc]

end ShiReversibleGenerator
