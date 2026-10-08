import ReversibleInitializationCapacityCopy
import ReversibleConstantTraversalResult

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

def constantComponentStart (cs : InitializationRegister → Nat) := Function.update cs (.inr 0) (cs (.inl 2))
def ascendingConstantComponentStart (cs : InitializationRegister → Nat) := Function.update cs (.inr 11) (cs (.inl 2))

theorem constantComponentStart_invariant (cs : InitializationRegister → Nat) (n : Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (pc : Option (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3))) (ys : List Bool) :
    constantCellInvariant header stackRank symbolCard backward ars (cs (.inl 2)) n (cs (.inl 2))
      ⟨pc, constantComponentStart cs, ys⟩ := by
  exact ⟨le_rfl, by simpa [constantComponentStart] using hn, by simp [constantComponentStart],
    by simpa [constantComponentStart] using hb, by simpa [constantComponentStart] using ht⟩

theorem ascendingConstantComponentStart_invariant (cs : InitializationRegister → Nat) (n : Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = 0) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (pc : Option (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) (ys : List Bool) :
    ascendingConstantCellInvariant header stackRank symbolCard backward ars (cs (.inl 2)) n (cs (.inl 2))
      ⟨pc, ascendingConstantComponentStart cs, ys⟩ := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ascendingConstantComponentStart, hi]
  · simpa [ascendingConstantComponentStart] using hn
  · simp [ascendingConstantComponentStart]
  · simpa [ascendingConstantComponentStart] using hb
  · simpa [ascendingConstantComponentStart] using ht

end ShiReversibleGenerator
