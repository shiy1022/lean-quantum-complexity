import ReversibleInitializationFieldBound
import ReversibleCounterBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding

theorem locatedInitialization_counterBudget (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) (bound : Nat)
    (h : CounterBudget cs (.inr 10) bound) (hi : cs (.inr 0) + 1 ≤ bound)
    (hb : cs (.inl 0) + 18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + symbolRank) + 18 ≤ bound) :
    CounterBudget (locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs) (.inr 10) bound := by
  let coord := header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + symbolRank
  let prepared := cellCoordinateResult header stackRank symbolCard symbolRank cs
  have hp : CounterBudget prepared (.inr 10) bound := by
    rw [show prepared = Function.update cs (.inr 1) coord by exact cellCoordinateResult_eq _ _ _ _ cs]
    exact h.update (.inr 1) coord (by dsimp [coord]; omega)
  have hn : prepared (.inl 0) = cs (.inl 0) := by simp [prepared, cellCoordinateResult_eq]
  have hidx : prepared (.inr 0) = cs (.inr 0) := by simp [prepared, cellCoordinateResult_eq]
  have hcoord : prepared (.inr 1) = coord := by simp [prepared, cellCoordinateResult_eq, coord]
  have ha : CounterBudget (initializationAddressResult prepared) (.inr 10) bound := by
    rw [initializationAddress_result]
    apply CounterBudget.update
    · apply CounterBudget.update
      · apply CounterBudget.update
        · apply CounterBudget.update
          · apply CounterBudget.update hp
            rw [hn, hcoord]
            dsimp [coord]
            omega
          · rw [hn, hcoord]
            dsimp [coord]
            omega
        · rw [hidx]; exact hi
      · omega
    · omega
  have hf := locatedInitialization_fields_bound header stackRank symbolCard symbolRank tm e a backward cs bound
    (by omega) hb
  intro r hr
  by_cases h7 : r = (Sum.inr 7 : InitializationRegister)
  · subst r; exact hf.1
  by_cases h8 : r = (Sum.inr 8 : InitializationRegister)
  · subst r; exact hf.2.1
  by_cases h9 : r = (Sum.inr 9 : InitializationRegister)
  · subst r; exact hf.2.2
  rw [locatedInitializationCounters, initializationInputBodyCounters, fixedNodeCounters_other]
  · exact ha r hr
  · simpa [initializationNodeRegisters] using h7
  · simpa [initializationNodeRegisters] using h8
  · simpa [initializationNodeRegisters] using h9
  · simpa [initializationNodeRegisters] using hr

end ShiReversibleGenerator
