import ReversibleTickSymbolRowFrames
import ReversibleTickSymbolRowDescendingTraversal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickSymbolRowDescendingBytes (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (input capacity outputBase : Nat) : Nat → List Bool
  | 0 => []
  | k + 1 => tickSymbolRowDescendingBytes tm stack inputStride bound backward input capacity outputBase k ++
      tickSymbolRowPayload tm stack inputStride bound backward input capacity outputBase k

/-- Actual descending emission prepends low-coordinate blocks in the established ascending forest order. -/
theorem tickSymbolRowDescendingResult_output (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (count : Nat)
    (s : CounterCfg (FixedLeafRegister (tickTraversalSupply tm))
      ((tickSymbolRowTemplate tm stack inputStride bound backward).Labels (Fin 3))) :
    let p := tickSymbolRowTemplate tm stack inputStride bound backward
    (descendingResult (programDescendingBody p (.inl 2)) count s).output =
      tickSymbolRowDescendingBytes tm stack inputStride bound backward (s.counters (.inl 0))
        (s.counters (.inl 1)) (s.counters (tickTraversalSpare tm 2)) count ++ s.output := by
  let p := tickSymbolRowTemplate tm stack inputStride bound backward
  induction count generalizing s with
  | zero => simp [descendingResult, tickSymbolRowDescendingBytes]
  | succ k ih =>
    let t := programDescendingBody p (.inl 2) k s
    have h0 : t.counters (.inl 0) = s.counters (.inl 0) := by
      change p.counters (Function.update s.counters (.inl 2) k) (.inl 0) = _
      rw [tickSymbolRowTemplate_control_frame tm stack inputStride bound backward _ 0 (by decide)]
      simp
    have h1 : t.counters (.inl 1) = s.counters (.inl 1) := by
      change p.counters (Function.update s.counters (.inl 2) k) (.inl 1) = _
      rw [tickSymbolRowTemplate_control_frame tm stack inputStride bound backward _ 1 (by decide)]
      simp
    have ho : t.counters (tickTraversalSpare tm 2) = s.counters (tickTraversalSpare tm 2) := by
      change p.counters (Function.update s.counters (.inl 2) k) (tickTraversalSpare tm 2) = _
      rw [tickSymbolRowTemplate_spare_frame]
      simp [tickTraversalSpare]
    have hy : t.output = tickSymbolRowPayload tm stack inputStride bound backward
        (s.counters (.inl 0)) (s.counters (.inl 1)) (s.counters (tickTraversalSpare tm 2)) k ++ s.output := by
      change p.bytes (Function.update s.counters (.inl 2) k) ++ s.output = _
      rw [tickSymbolRowTemplate_payload_eq]
      simp [tickTraversalSpare]
    change (descendingResult (programDescendingBody p (.inl 2)) k t).output = _
    rw [ih, h0, h1, ho, hy]
    simp only [tickSymbolRowDescendingBytes, List.append_assoc]

end ShiReversibleGenerator
