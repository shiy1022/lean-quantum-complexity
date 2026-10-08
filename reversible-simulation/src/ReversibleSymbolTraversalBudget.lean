import ReversibleSymbolCounterBudget
import ReversibleSymbolCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

def SymbolCellBudgetInvariant (bound layers capacity n k : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))) : Prop :=
  symbolCellInvariant header stackRank symbolCard tm e backward ars capacity n k s ∧
    CounterBudget s.counters (.inr 10) bound ∧
      s.counters (.inr 10) ≤ layers + (capacity - k) * (ars.length * 630)

/-- The loop maintains a fixed address budget and a separate linear layer-count budget. -/
theorem symbolCellBudget_next (bound layers capacity n k : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    (hb : ∀ ar ∈ ars, n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 ≤ bound)
    (hs : SymbolCellBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n (k + 1) s) :
    SymbolCellBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n k
      (symbolCellBody header stackRank symbolCard tm e backward ars capacity n k s) := by
  have hk := hs.1.1
  have hc : capacity ≤ bound := by
    simpa [hs.1.2.2.1] using hs.2.1 (.inl 2) (by decide)
  let cs := Function.update s.counters (Sum.inr 0 : InitializationRegister) k
  have hcs : CounterBudget cs (.inr 10) bound := hs.2.1.update (.inr 0) k (by omega)
  have hidx : cs (.inr 0) + 1 ≤ bound := by simp only [cs, Function.update_self]; omega
  have haddr : ∀ ar ∈ ars, cs (.inl 0) +
      18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2) + 18 ≤ bound := by
    intro ar har
    simp only [cs, Function.update_self]
    simp [hs.1.2.1, hs.1.2.2.1]
    calc
      n + 18 * (header + (stackRank * capacity + k) * symbolCard + ar.2) + 18 ≤
          n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 := by gcongr; omega
      _ ≤ bound := hb ar har
  have hnext := symbolSequence_counterBudget header stackRank symbolCard tm e backward ars cs bound hcs hidx haddr
  have hlayer : (symbolCellBody header stackRank symbolCard tm e backward ars capacity n k s).counters (.inr 10) ≤
      s.counters (.inr 10) + ars.length * 630 := by
    simpa [symbolCellBody, cs] using symbolSequence_layer_bound header stackRank symbolCard tm e backward ars cs
  refine ⟨symbolCellBody_invariant header stackRank symbolCard tm e backward ars capacity n k s hs.1, hnext, ?_⟩
  have hsub : capacity - k = capacity - (k + 1) + 1 := by omega
  rw [hsub, Nat.add_mul, Nat.one_mul]
  have hprev := hs.2.2
  omega

/-- The entire concrete symbol/cell loop has a polynomial clock, not merely a polynomial payload length. -/
theorem symbolCellTraversal_polynomial_bound (capacity budget layers : Polynomial Nat)
    (hb : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))),
      SymbolCellBudgetInvariant header stackRank symbolCard tm e backward ars (budget.eval n) (layers.eval n) (capacity.eval n) n count s →
      descendingSteps (symbolCellBody header stackRank symbolCard tm e backward ars (capacity.eval n) n)
        (symbolCellCost header stackRank symbolCard tm e backward ars) count s ≤ clock.eval n := by
  let totalLayers := layers + capacity * Polynomial.C (ars.length * 630)
  obtain ⟨unitClock, hunit⟩ := symbolSequence_polynomial_bound header stackRank symbolCard tm e backward ars budget totalLayers
  refine ⟨capacity * (unitClock + Polynomial.C 2) + Polynomial.C 1, ?_⟩
  intro n count s hs
  let invariant := SymbolCellBudgetInvariant header stackRank symbolCard tm e backward ars (budget.eval n) (layers.eval n) (capacity.eval n) n
  have hcost : ∀ k t, invariant (k + 1) t → symbolCellCost header stackRank symbolCard tm e backward ars k t ≤ unitClock.eval n := by
    intro k t ht
    have hk := ht.1.1
    have hc : capacity.eval n ≤ budget.eval n := by
      simpa [ht.1.2.2.1] using ht.2.1 (.inl 2) (by decide)
    let cs := Function.update t.counters (Sum.inr 0 : InitializationRegister) k
    apply hunit n cs
    · exact ht.2.1.update (.inr 0) k (by omega)
    · have hm := Nat.mul_le_mul_right (ars.length * 630) (Nat.sub_le (capacity.eval n) (k + 1))
      have hl := ht.2.2
      simp only [totalLayers, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      simp [cs]
      omega
    · simp only [cs, Function.update_self]; omega
    · intro ar har
      simp only [cs, Function.update_self]
      simp [ht.1.2.1, ht.1.2.2.1]
      calc
        n + 18 * (header + (stackRank * capacity.eval n + k) * symbolCard + ar.2) + 18 ≤
            n + 18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 := by gcongr; omega
        _ ≤ budget.eval n := hb n ar har
  have hrun := descendingSteps_bound
    (symbolCellBody header stackRank symbolCard tm e backward ars (capacity.eval n) n)
    (symbolCellCost header stackRank symbolCard tm e backward ars) (unitClock.eval n) invariant hcost
    (fun k t ht => symbolCellBudget_next header stackRank symbolCard tm e backward ars
      (budget.eval n) (layers.eval n) (capacity.eval n) n k t (hb n) ht) count s hs
  have hk := hs.1.1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  exact hrun.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1)

end ShiReversibleGenerator
