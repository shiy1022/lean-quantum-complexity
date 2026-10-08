import ReversibleTickStackTraversalFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickStackTraversalTemplate_ready_preserved (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (hr : fixedGuardedEmitterReady (tickTraversalSupply tm) cs) :
    fixedGuardedEmitterReady (tickTraversalSupply tm)
      ((tickStackTraversalTemplate tm stack inputStride strideBound backward).counters cs) := by
  unfold fixedGuardedEmitterReady at hr ⊢
  have hf := tickStackTraversalTemplate_control_frame tm stack inputStride strideBound backward cs
  rcases hr with ⟨h3,h4,h5,h10,h11⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hf 3 (by decide) (by decide)]; exact h3
  · rw [hf 4 (by decide) (by decide)]; exact h4
  · rw [hf 5 (by decide) (by decide)]; exact h5
  · rw [hf 10 (by decide) (by decide)]; exact h10
  · rw [hf 11 (by decide) (by decide)]; exact h11

theorem tickStackTraversalTemplate_windows_preserved (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride strideBound : Nat) (backward : Bool) (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat)
    (wireBound : Nat) (hw : TickWindowBudget tm inputStride strideBound wireBound cs) :
    TickWindowBudget tm inputStride strideBound wireBound
      ((tickStackTraversalTemplate tm stack inputStride strideBound backward).counters cs) := by
  unfold TickWindowBudget
  rw [tickStackTraversalTemplate_control_frame tm stack inputStride strideBound backward cs 0 (by decide) (by decide),
    tickStackTraversalTemplate_control_frame tm stack inputStride strideBound backward cs 1 (by decide) (by decide),
    tickStackTraversalTemplate_spare_frame tm stack inputStride strideBound backward cs 2 (by decide)]
  exact hw

end ShiReversibleGenerator
