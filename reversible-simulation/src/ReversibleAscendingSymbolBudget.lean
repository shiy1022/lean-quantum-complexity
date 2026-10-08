import ReversibleAscendingSymbolCellTraversal
import ReversibleSymbolCounterBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

def AscendingSymbolBudgetInvariant (bound layers capacity n k : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) : Prop :=
  ascendingSymbolCellInvariant header stackRank symbolCard tm e backward ars capacity n k s ∧
    CounterBudget s.counters (.inr 10) bound ∧
      s.counters (.inr 10) ≤ layers + (capacity - k) * (ars.length * 630)

theorem ascendingSymbolBudget_next (bound layers capacity n k : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (hb : ∀ ar ∈ ars, n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 ≤ bound)
    (hs : AscendingSymbolBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n (k + 1) s) :
    AscendingSymbolBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n k
      (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n k s) := by
  rcases hs.1 with ⟨hk, hi, hn, hcap, hbuf, htmp⟩
  have hc : capacity ≤ bound := by
    simpa [hcap] using hs.2.1 (.inl 2) (by decide)
  let cs := Function.update s.counters (Sum.inr 11 : InitializationRegister) k
  have hcs : CounterBudget cs (.inr 10) bound := hs.2.1.update (.inr 11) k (by omega)
  have hidx : cs (.inr 0) + 1 ≤ bound := by simp [cs]; omega
  have haddr : ∀ ar ∈ ars, cs (.inl 0) +
      18 * (header + (stackRank * cs (.inl 2) + cs (.inr 0)) * symbolCard + ar.2) + 18 ≤ bound := by
    intro ar har
    simp [cs, hn, hcap]
    calc
      n + 18 * (header + (stackRank * capacity + s.counters (.inr 0)) * symbolCard + ar.2) + 18 ≤
          n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 := by gcongr; omega
      _ ≤ bound := hb ar har
  have hnext := symbolSequence_counterBudget header stackRank symbolCard tm e backward ars cs bound hcs hidx haddr
  have hbudget : CounterBudget
      (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n k s).counters (.inr 10) bound :=
    hnext.update (.inr 0) (s.counters (.inr 0) + 1) (by omega)
  have hlayer : (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n k s).counters (.inr 10) ≤
      s.counters (.inr 10) + ars.length * 630 := by
    simpa [ascendingSymbolCellBody, cs] using symbolSequence_layer_bound header stackRank symbolCard tm e backward ars cs
  refine ⟨ascendingSymbolCellBody_invariant header stackRank symbolCard tm e backward ars capacity n k s hs.1, hbudget, ?_⟩
  have hsub : capacity - k = capacity - (k + 1) + 1 := by omega
  rw [hsub, Nat.add_mul, Nat.one_mul]
  have hprev := hs.2.2
  omega

/-- The whole ascending traversal, including its actual index increments, has a polynomial clock. -/
theorem ascendingSymbolTraversal_polynomial_bound (capacity budget layers : Polynomial Nat)
    (hb : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))),
      AscendingSymbolBudgetInvariant header stackRank symbolCard tm e backward ars (budget.eval n) (layers.eval n) (capacity.eval n) n count s →
      descendingSteps (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars (capacity.eval n) n)
        (ascendingSymbolCellCost header stackRank symbolCard tm e backward ars) count s ≤ clock.eval n := by
  let totalLayers := layers + capacity * Polynomial.C (ars.length * 630)
  obtain ⟨unitClock, hunit⟩ := symbolSequence_polynomial_bound header stackRank symbolCard tm e backward ars budget totalLayers
  refine ⟨capacity * (unitClock + Polynomial.C 3) + Polynomial.C 1, ?_⟩
  intro n count s hs
  let invariant := AscendingSymbolBudgetInvariant header stackRank symbolCard tm e backward ars (budget.eval n) (layers.eval n) (capacity.eval n) n
  have hcost : ∀ k t, invariant (k + 1) t → ascendingSymbolCellCost header stackRank symbolCard tm e backward ars k t ≤ unitClock.eval n + 1 := by
    intro k t ht
    rcases ht.1 with ⟨hk, hi, hn, hcap, hbuf, htmp⟩
    have hc : capacity.eval n ≤ budget.eval n := by
      simpa [hcap] using ht.2.1 (.inl 2) (by decide)
    let cs := Function.update t.counters (Sum.inr 11 : InitializationRegister) k
    have hr : symbolSequenceSteps header stackRank symbolCard tm e backward ars cs ≤ unitClock.eval n := by
      apply hunit n cs
      · exact ht.2.1.update (.inr 11) k (by omega)
      · have hm := Nat.mul_le_mul_right (ars.length * 630) (Nat.sub_le (capacity.eval n) (k + 1))
        have hl := ht.2.2
        simp only [totalLayers, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        simp [cs]
        omega
      · simp [cs]; omega
      · intro ar har
        simp [cs, hn, hcap]
        calc
          n + 18 * (header + (stackRank * capacity.eval n + t.counters (.inr 0)) * symbolCard + ar.2) + 18 ≤
              n + 18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 := by gcongr; omega
          _ ≤ budget.eval n := hb n ar har
    exact Nat.add_le_add_right hr 1
  have hrun := descendingSteps_bound
    (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars (capacity.eval n) n)
    (ascendingSymbolCellCost header stackRank symbolCard tm e backward ars) (unitClock.eval n + 1) invariant hcost
    (fun k t ht => ascendingSymbolBudget_next header stackRank symbolCard tm e backward ars
      (budget.eval n) (layers.eval n) (capacity.eval n) n k t (hb n) ht) count s hs
  have hk := hs.1.1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have hbound := hrun.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1)
  simpa [Nat.add_assoc] using hbound

end ShiReversibleGenerator
