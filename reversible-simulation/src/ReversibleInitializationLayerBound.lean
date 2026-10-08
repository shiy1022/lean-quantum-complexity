import ReversibleLocatedBodyBounds
import ReversibleInitializationSymbolSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding ShiReversibleFormula

theorem initializationInputBody_layer_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool) (cs : InitializationRegister → Nat) :
    initializationInputBodyCounters tm e a backward cs (.inr 10) ≤ cs (.inr 10) + 630 := by
  classical
  change fixedNodeCounters initializationNodeRegisters (initializationInputSelection tm e a backward cs)
    (initializationAddressResult cs) initializationNodeRegisters.count ≤ _
  rw [fixedNodeCounters_count _ _ (by decide) (by decide) (by decide)]
  have hy := formulaElementaryLayers_bound (initializationInputCellSchema tm e a)
  have hs := initializationInputCellSchema_size tm e a
  have hn := formulaElementaryLayers_bound (.constant (oneHot none a) : Formula Unit)
  simp only [initializationInputSelection]
  split_ifs <;>
    simp only [initializationInputYes, initializationInputNo, initializationYesTemplates,
      initializationNoTemplates, paddedFormulaPrinter_layer_count]
  all_goals simp only [initializationNodeRegisters, initializationAddress_result] at *
  all_goals simp only [Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 6),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 5),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 4),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 3),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 2)]
  · omega
  · simp only [formulaElementaryLayers]
    split_ifs <;> omega

theorem locatedInitialization_layer_bound (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (a : Option (MachineSymbol tm))
    (backward : Bool) (cs : InitializationRegister → Nat) :
    locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs (.inr 10) ≤
      cs (.inr 10) + 630 := by
  simpa [locatedInitializationCounters, cellCoordinateResult_eq] using
    initializationInputBody_layer_bound tm e a backward
      (cellCoordinateResult header stackRank symbolCard symbolRank cs)

theorem symbolSequence_layer_bound (header stackRank symbolCard : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)
    (ars : List (Option (MachineSymbol tm) × Nat)) (cs : InitializationRegister → Nat) :
    symbolSequenceCounters header stackRank symbolCard tm e backward ars cs (.inr 10) ≤
      cs (.inr 10) + ars.length * 630 := by
  induction ars generalizing cs with
  | nil => simp [symbolSequenceCounters]
  | cons ar ars ih =>
      have h := ih (locatedInitializationCounters header stackRank symbolCard ar.2 tm e ar.1 backward cs)
      have hb := locatedInitialization_layer_bound header stackRank symbolCard ar.2 tm e ar.1 backward cs
      simp only [symbolSequenceCounters, List.length_cons, Nat.succ_mul]
      omega

end ShiReversibleGenerator
