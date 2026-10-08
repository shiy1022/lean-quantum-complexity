import ReversibleConstantComponentStart
import ReversibleAscendingSymbolCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))


theorem inputComponentStart_invariant (cs : InitializationRegister → Nat) (n : Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (pc : Option (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))) (ys : List Bool) :
    symbolCellInvariant header stackRank symbolCard tm e backward ars (cs (.inl 2)) n (cs (.inl 2))
      ⟨pc, constantComponentStart cs, ys⟩ := by
  exact ⟨le_rfl, by simpa [constantComponentStart] using hn, by simp [constantComponentStart],
    by simpa [constantComponentStart] using hb, by simpa [constantComponentStart] using ht⟩

theorem ascendingInputComponentStart_invariant (cs : InitializationRegister → Nat) (n : Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = 0) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (pc : Option (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) (ys : List Bool) :
    ascendingSymbolCellInvariant header stackRank symbolCard tm e backward ars (cs (.inl 2)) n (cs (.inl 2))
      ⟨pc, ascendingConstantComponentStart cs, ys⟩ := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ascendingConstantComponentStart, hi]
  · simpa [ascendingConstantComponentStart] using hn
  · simp [ascendingConstantComponentStart]
  · simpa [ascendingConstantComponentStart] using hb
  · simpa [ascendingConstantComponentStart] using ht

end ShiReversibleGenerator
