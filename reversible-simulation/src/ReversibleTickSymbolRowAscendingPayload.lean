import ReversibleTickSymbolRowFrames
import ReversibleTickSymbolRowAscendingTraversal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickSymbolRowAscendingBytes (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (input capacity outputBase : Nat) : Nat → Nat → List Bool
  | _, 0 => []
  | position, k + 1 =>
      tickSymbolRowAscendingBytes tm stack inputStride bound backward input capacity outputBase (position + 1) k ++
      tickSymbolRowPayload tm stack inputStride bound backward input capacity outputBase position

/-- Increasing actual traversal prepends coordinate blocks in reverse forest order. -/
theorem tickSymbolRowAscendingResult_output (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickSymbolRowAscendingBody tm stack inputStride bound backward).Labels (Fin 3))) :
    let p := tickSymbolRowAscendingBody tm stack inputStride bound backward
    let remaining := tickTraversalSpare tm 0
    (descendingResult (programDescendingBody p remaining) count s).output =
      tickSymbolRowAscendingBytes tm stack inputStride bound backward (s.counters (.inl 0))
        (s.counters (.inl 1)) (s.counters (tickTraversalSpare tm 2)) (s.counters (.inl 2)) count ++ s.output := by
  let p := tickSymbolRowAscendingBody tm stack inputStride bound backward
  let remaining := tickTraversalSpare tm 0
  induction count generalizing s with
  | zero => simp [descendingResult, tickSymbolRowAscendingBytes]
  | succ k ih =>
    let t := programDescendingBody p remaining k s
    have h0 : t.counters (.inl 0) = s.counters (.inl 0) := by
      let after := (tickSymbolRowTemplate tm stack inputStride bound backward).counters
        (Function.update s.counters remaining k)
      change Function.update after (.inl 2) (after (.inl 2) + 1) (.inl 0) = _
      rw [Function.update_of_ne (by simp : (Sum.inl (0 : Fin 14) : FixedLeafRegister (tickTraversalSupply tm)) ≠ .inl 2)]
      dsimp only [after]
      rw [tickSymbolRowTemplate_control_frame tm stack inputStride bound backward _ 0 (by decide)]
      simp [remaining, tickTraversalSpare]
    have h1 : t.counters (.inl 1) = s.counters (.inl 1) := by
      change p.counters (Function.update s.counters remaining k) (.inl 1) = _
      rw [tickSymbolRowAscendingBody_capacity]
      simp [remaining, tickTraversalSpare]
    have ho : t.counters (tickTraversalSpare tm 2) = s.counters (tickTraversalSpare tm 2) := by
      change p.counters (Function.update s.counters remaining k) (tickTraversalSpare tm 2) = _
      rw [tickSymbolRowAscendingBody_spare_frame]
      have hn : tickTraversalSpare tm 2 ≠ remaining := by simp [remaining, tickTraversalSpare, Fin.ext_iff]
      simp [hn]
    have hp : t.counters (.inl 2) = s.counters (.inl 2) + 1 := by
      change p.counters (Function.update s.counters remaining k) (.inl 2) = _
      rw [tickSymbolRowAscendingBody_position]
      simp [remaining, tickTraversalSpare]
    have hy : t.output = tickSymbolRowPayload tm stack inputStride bound backward
        (s.counters (.inl 0)) (s.counters (.inl 1)) (s.counters (tickTraversalSpare tm 2))
        (s.counters (.inl 2)) ++ s.output := by
      change p.bytes (Function.update s.counters remaining k) ++ s.output = _
      simp only [p, tickSymbolRowAscendingBody, sequenceProgramTemplate, incrementProgramTemplate, List.nil_append]
      rw [tickSymbolRowTemplate_payload_eq]
      have hn : tickTraversalSpare tm 2 ≠ remaining := by simp [remaining, tickTraversalSpare, Fin.ext_iff]
      simp [remaining, tickTraversalSpare, hn, Fin.ext_iff]
    change (descendingResult (programDescendingBody p remaining) k t).output = _
    rw [ih, h0, h1, ho, hp, hy]
    simp only [tickSymbolRowAscendingBytes, List.append_assoc]

end ShiReversibleGenerator
