import ReversibleSymbolCellTraversal
import ReversibleSymbolAscendingControl

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

/-- The descending traversal's designated exit can be joined to a following finite program. -/
theorem symbolCellLoop_exit :
    symbolCellLoopCode header stackRank symbolCard tm e backward ars
      (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3)) = .halt := by
  classical
  have h20 : symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3) ≠
      symbolSequenceExit header stackRank symbolCard tm e backward ars 0 :=
    fun h => (by decide : (2 : Fin 3) ≠ 0)
      (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  have h21 : symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3) ≠
      symbolSequenceExit header stackRank symbolCard tm e backward ars 1 :=
    fun h => (by decide : (2 : Fin 3) ≠ 1)
      (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  simp [symbolCellLoopCode, reentryCode, h20, h21, symbolSequenceCode_embed, CounterInstr.relabel]

/-- The ascending traversal also exposes its distinct designated exit. -/
theorem symbolAscending_exit :
    symbolAscendingCode header stackRank symbolCard tm e backward ars
      (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4)) = .halt := by
  classical
  have h30 : symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4) ≠
      symbolSequenceExit header stackRank symbolCard tm e backward ars 0 :=
    fun h => (by decide : (3 : Fin 4) ≠ 0)
      (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  have h31 : symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4) ≠
      symbolSequenceExit header stackRank symbolCard tm e backward ars 1 :=
    fun h => (by decide : (3 : Fin 4) ≠ 1)
      (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  have h32 : symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4) ≠
      symbolSequenceExit header stackRank symbolCard tm e backward ars 2 :=
    fun h => (by decide : (3 : Fin 4) ≠ 2)
      (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)
  simp [symbolAscendingCode, h30, h31, h32, symbolSequenceCode_embed, CounterInstr.relabel]

end ShiReversibleGenerator
