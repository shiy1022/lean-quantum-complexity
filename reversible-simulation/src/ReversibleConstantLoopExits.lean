import ReversibleConstantSequenceControl
import ReversibleConstantAscendingControl

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

/-- The descending traversal's designated exit can be joined to a following finite program. -/
theorem constantCellLoop_exit :
    constantCellLoopCode header stackRank symbolCard backward ars
      (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3)) = .halt := by
  classical
  have h20 : constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3) ≠
      constantSequenceExit header stackRank symbolCard backward ars 0 :=
    fun h => (by decide : (2 : Fin 3) ≠ 0)
      (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  have h21 : constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3) ≠
      constantSequenceExit header stackRank symbolCard backward ars 1 :=
    fun h => (by decide : (2 : Fin 3) ≠ 1)
      (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  simp [constantCellLoopCode, reentryCode, h20, h21, constantSequenceCode_embed, CounterInstr.relabel]

/-- The ascending traversal also exposes its distinct designated exit. -/
theorem constantAscending_exit :
    constantAscendingCode header stackRank symbolCard backward ars
      (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4)) = .halt := by
  classical
  have h30 : constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4) ≠
      constantSequenceExit header stackRank symbolCard backward ars 0 :=
    fun h => (by decide : (3 : Fin 4) ≠ 0)
      (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  have h31 : constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4) ≠
      constantSequenceExit header stackRank symbolCard backward ars 1 :=
    fun h => (by decide : (3 : Fin 4) ≠ 1)
      (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  have h32 : constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4) ≠
      constantSequenceExit header stackRank symbolCard backward ars 2 :=
    fun h => (by decide : (3 : Fin 4) ≠ 2)
      (constantSequenceExit_injective header stackRank symbolCard backward ars h)
  simp [constantAscendingCode, h30, h31, h32, constantSequenceCode_embed, CounterInstr.relabel]

end ShiReversibleGenerator
